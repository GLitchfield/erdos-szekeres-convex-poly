module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 348. -/

theorem es6Anchored_clause44544 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44545 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44546 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44547 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44548 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44549 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44550 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44551 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44552 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 14] (by decide)
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

theorem es6Anchored_clause44553 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44554 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44555 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44556 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44557 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44558 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44559 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44560 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44561 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44562 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 15] (by decide)
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

theorem es6Anchored_clause44563 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 16] (by decide)
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

theorem es6Anchored_clause44564 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 16] (by decide)
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

theorem es6Anchored_clause44565 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 16] (by decide)
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

theorem es6Anchored_clause44566 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 16] (by decide)
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

theorem es6Anchored_clause44567 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 13, 16] (by decide)
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

theorem es6Anchored_clause44568 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44569 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44570 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44571 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44572 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44573 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44574 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44575 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44576 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 15] (by decide)
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

theorem es6Anchored_clause44577 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 16] (by decide)
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

theorem es6Anchored_clause44578 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 16] (by decide)
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

theorem es6Anchored_clause44579 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 16] (by decide)
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

theorem es6Anchored_clause44580 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 16] (by decide)
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

theorem es6Anchored_clause44581 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 14, 16] (by decide)
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

theorem es6Anchored_clause44582 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 15, 16] (by decide)
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

theorem es6Anchored_clause44583 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 15, 16] (by decide)
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

theorem es6Anchored_clause44584 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 15, 16] (by decide)
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

theorem es6Anchored_clause44585 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 15, 16] (by decide)
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

theorem es6Anchored_clause44586 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 12, 15, 16] (by decide)
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

theorem es6Anchored_clause44587 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44588 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44589 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44590 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44591 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44592 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44593 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44594 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44595 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44596 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 15] (by decide)
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

theorem es6Anchored_clause44597 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 16] (by decide)
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

theorem es6Anchored_clause44598 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 16] (by decide)
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

theorem es6Anchored_clause44599 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 16] (by decide)
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

theorem es6Anchored_clause44600 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 16] (by decide)
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

theorem es6Anchored_clause44601 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 14, 16] (by decide)
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

theorem es6Anchored_clause44602 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 15, 16] (by decide)
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

theorem es6Anchored_clause44603 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 15, 16] (by decide)
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

theorem es6Anchored_clause44604 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 15, 16] (by decide)
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

theorem es6Anchored_clause44605 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 13, 15, 16] (by decide)
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

theorem es6Anchored_clause44606 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause44607 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause44608 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause44609 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause44610 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 6, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause44611 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44612 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44613 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44614 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44615 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44616 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44617 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44618 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44619 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44620 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44621 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44622 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause44623 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
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

theorem es6Anchored_clause44624 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44625 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44626 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44627 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44628 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44629 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44630 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44631 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44632 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44633 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44634 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause44635 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.right) (x8 := Turn.right) (x9 := Turn.left) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.right) (x14 := Turn.right) (x15 := Turn.left) (x16 := Turn.right) (x17 := Turn.right) (x18 := Turn.left) (x19 := Turn.left)
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

theorem es6Anchored_clause44636 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
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

theorem es6Anchored_clause44637 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44638 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44639 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44640 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44641 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44642 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44643 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44644 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44645 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44646 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44647 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause44648 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
  have hm := strongSix_mismatch chi f (hno f) (x0 := Turn.right) (x1 := Turn.right) (x2 := Turn.right) (x3 := Turn.right) (x4 := Turn.right) (x5 := Turn.right) (x6 := Turn.right) (x7 := Turn.left) (x8 := Turn.left) (x9 := Turn.right) (x10 := Turn.right) (x11 := Turn.right) (x12 := Turn.right) (x13 := Turn.left) (x14 := Turn.left) (x15 := Turn.right) (x16 := Turn.left) (x17 := Turn.left) (x18 := Turn.right) (x19 := Turn.right)
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

theorem es6Anchored_clause44649 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44650 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44651 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44652 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44653 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44654 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44655 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44656 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44657 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44658 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44659 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause44660 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44661 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44662 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44663 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44664 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44665 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44666 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44667 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44668 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44669 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44670 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause44671 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![4, 5, 7, 8, 9, 14] (by decide)
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
