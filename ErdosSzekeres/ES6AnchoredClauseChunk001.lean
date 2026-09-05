module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres.ES6

/-! Retained anchored ES(6) semantic clauses, group 001. -/

theorem es6Anchored_clause00128 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00129 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00130 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00131 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00132 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00133 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00134 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00135 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00136 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00137 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00138 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00139 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00140 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00141 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00142 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00143 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00144 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00145 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00146 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00147 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00148 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00149 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00150 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00151 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00152 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00153 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00154 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00155 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00156 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00157 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00158 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00159 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00160 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00161 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00162 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00163 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00164 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00165 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00166 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00167 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00168 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00169 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00170 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00171 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00172 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00173 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00174 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00175 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00176 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00177 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00178 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00179 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00180 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00181 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00182 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00183 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00184 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00185 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00186 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00187 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00188 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00189 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00190 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00191 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00192 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00193 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00194 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00195 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00196 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00197 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00198 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00199 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 4 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00200 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00201 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00202 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00203 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00204 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00205 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00206 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00207 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 6 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00208 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00209 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00210 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00211 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00212 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00213 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00214 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00215 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 7 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00216 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00217 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00218 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00219 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00220 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00221 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00222 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00223 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00224 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00225 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00226 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00227 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00228 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00229 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00230 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00231 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00232 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00233 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00234 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00235 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00236 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00237 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00238 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00239 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00240 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00241 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00242 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00243 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00244 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00245 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00246 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00247 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00248 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00249 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause00250 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00251 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00252 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause00253 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause00254 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause00255 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 1 2 5 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

end ErdosSzekeres.ES6

end
