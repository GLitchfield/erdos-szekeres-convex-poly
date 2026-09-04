module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 168. -/

theorem es6Anchored_clause21504 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 12, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21505 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 12, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21506 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 12, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21507 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 12, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21508 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 12, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21509 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 13, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21510 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 13, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21511 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 13, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21512 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 14, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21513 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 14, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21514 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨11, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 11, 15, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21515 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 12, 13, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21516 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 12, 13, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21517 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 12, 13, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21518 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 12, 14, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21519 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 12, 14, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21520 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 12, 15, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21521 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 13, 14, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21522 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 13, 14, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21523 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 13, 15, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21524 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 6, 14, 15, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21525 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
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
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21526 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21527 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21528 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21529 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21530 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21531 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21532 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21533 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21534 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21535 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 10] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21536 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21537 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21538 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21539 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21540 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21541 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21542 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21543 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21544 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21545 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21546 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21547 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21548 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21549 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21550 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21551 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21552 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21553 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21554 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21555 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21556 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21557 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 9, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21558 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21559 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21560 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21561 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21562 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21563 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21564 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21565 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21566 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21567 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21568 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21569 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21570 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21571 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21572 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21573 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21574 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21575 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21576 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21577 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21578 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 10, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21579 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21580 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21581 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21582 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21583 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21584 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21585 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21586 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21587 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21588 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21589 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 11, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21590 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21591 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21592 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21593 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21594 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21595 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21596 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21597 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 12, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21598 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 13, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21599 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 13, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21600 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 13, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21601 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 14, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21602 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 14, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21603 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 8, 15, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21604 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
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
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21605 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21606 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21607 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.right) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hb15 hs
  · exact hb16 hs
  · exact hb17 hs
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21608 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21609 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21610 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21611 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21612 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21613 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hb4 hs
  · exact hb5 hs
  · exact hb6 hs
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21614 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21615 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21616 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21617 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21618 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21619 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21620 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21621 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 14] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21622 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
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
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21623 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 15] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21624 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 10, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 10, 16] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21625 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
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
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hb10 hs
  · exact hb11 hs
  · exact hb12 hs
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21626 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21627 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21628 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hb0 hs
  · exact hb1 hs
  · exact hb2 hs
  · exact hb3 hs
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21629 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hb7 hs
  · exact hb8 hs
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hb13 hs
  · exact hb14 hs
  · exact hs hb15
  · exact hb16 hs
  · exact hb17 hs
  · exact hs hb18
  · exact hs hb19

theorem es6Anchored_clause21630 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hb9 hs
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hb15 hs
  · exact hs hb16
  · exact hs hb17
  · exact hb18 hs
  · exact hb19 hs

theorem es6Anchored_clause21631 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨9, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 7, 9, 11, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.left) (x1 := Turn.left) (x2 := Turn.left) (x3 := Turn.left) (x4 := Turn.left) (x5 := Turn.left) (x6 := Turn.left) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.left) (x10 := Turn.left) (x11 := Turn.left) (x12 := Turn.left) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.left) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.left) (x19 := Turn.left)
    (by simp [StrongSixValues])
  simp only [f, Turn.ne_right_iff_eq_left] at hm
  rcases hbad with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18, hb19⟩
  rcases hm with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact hs hb0
  · exact hs hb1
  · exact hs hb2
  · exact hs hb3
  · exact hs hb4
  · exact hs hb5
  · exact hs hb6
  · exact hs hb7
  · exact hs hb8
  · exact hs hb9
  · exact hs hb10
  · exact hs hb11
  · exact hs hb12
  · exact hs hb13
  · exact hs hb14
  · exact hs hb15
  · exact hs hb16
  · exact hs hb17
  · exact hs hb18
  · exact hs hb19

end ErdosSzekeres

end
