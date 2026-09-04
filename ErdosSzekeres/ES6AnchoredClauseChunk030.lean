module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 030. -/

theorem es6Anchored_clause03840 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03841 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03842 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03843 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03844 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03845 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03846 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03847 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03848 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03849 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03850 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03851 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03852 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03853 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03854 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03855 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03856 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03857 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03858 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03859 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03860 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03861 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03862 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03863 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03864 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03865 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03866 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03867 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03868 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03869 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03870 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03871 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03872 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03873 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03874 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03875 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03876 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03877 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03878 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03879 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03880 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03881 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03882 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03883 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03884 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03885 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03886 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03887 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03888 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03889 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03890 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03891 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03892 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03893 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03894 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03895 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03896 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03897 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03898 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03899 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03900 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03901 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03902 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 6 16 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03903 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03904 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03905 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03906 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03907 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03908 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03909 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03910 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 8 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03911 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03912 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03913 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03914 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03915 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03916 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03917 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03918 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 9 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03919 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03920 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03921 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03922 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03923 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03924 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03925 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03926 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 10 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03927 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03928 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03929 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03930 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03931 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03932 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03933 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03934 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 11 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03935 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03936 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03937 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03938 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03939 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03940 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03941 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03942 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 12 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03943 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03944 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03945 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03946 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03947 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03948 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03949 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03950 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 13 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03951 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03952 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03953 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03954 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03955 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03956 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03957 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03958 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 14 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03959 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03960 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hb3 hs

theorem es6Anchored_clause03961 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03962 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.left) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hs hb1
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03963 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03964 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

theorem es6Anchored_clause03965 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.right) (C := Turn.left) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hb1 hs
  · exact hs hb2
  · exact hs hb3

theorem es6Anchored_clause03966 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 15 (by decide) (by decide) (by decide))
    (A := Turn.left) (B := Turn.left) (C := Turn.right) (D := Turn.left) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hb2 hs
  · exact hs hb3

theorem es6Anchored_clause03967 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨2, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  have hm := turnSequence_mismatch
    (hallowed 2 3 7 16 (by decide) (by decide) (by decide))
    (A := Turn.right) (B := Turn.right) (C := Turn.left) (D := Turn.right) (by simp [TurnSequenceAllowed])
  simp only [Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3⟩
  rcases hm with hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hs hb2
  · exact hb3 hs

end ErdosSzekeres

end
