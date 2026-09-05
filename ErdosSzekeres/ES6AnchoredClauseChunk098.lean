module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Retained anchored ES(6) semantic clauses, group 098. -/

theorem es6Anchored_clause12544 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 12 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12545 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 12 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12546 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 12 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12547 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12548 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12549 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12550 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12551 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12552 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12553 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12554 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12555 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12556 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12557 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12558 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12559 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12560 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12561 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12562 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12563 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12564 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12565 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12566 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12567 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12568 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12569 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12570 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12571 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12572 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12573 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12574 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 13 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12575 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12576 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12577 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12578 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12579 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12580 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12581 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12582 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12583 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12584 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12585 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12586 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12587 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12588 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12589 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12590 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 14 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12591 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12592 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12593 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12594 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12595 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12596 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12597 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12598 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 9 15 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12599 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12600 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12601 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12602 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12603 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12604 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12605 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12606 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12607 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12608 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12609 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12610 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12611 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12612 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12613 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12614 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12615 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12616 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12617 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12618 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12619 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12620 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12621 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12622 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12623 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12624 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12625 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12626 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12627 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12628 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12629 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12630 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12631 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12632 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12633 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12634 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12635 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12636 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12637 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12638 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 11 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12639 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12640 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12641 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12642 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12643 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12644 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12645 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12646 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12647 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12648 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12649 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12650 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12651 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12652 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12653 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12654 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12655 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12656 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12657 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12658 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12659 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12660 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12661 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12662 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12663 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12664 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause12665 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12666 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12667 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12668 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause12669 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause12670 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨10, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 12 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause12671 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨10, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 6 10 13 14 (by decide) (by decide) (by decide))
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
