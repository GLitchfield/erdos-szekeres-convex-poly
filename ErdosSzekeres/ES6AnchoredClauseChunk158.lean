module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 158. -/

theorem es6Anchored_clause20224 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 12] (by decide)
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

theorem es6Anchored_clause20225 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 13] (by decide)
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

theorem es6Anchored_clause20226 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 13] (by decide)
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

theorem es6Anchored_clause20227 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 13] (by decide)
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

theorem es6Anchored_clause20228 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 13] (by decide)
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

theorem es6Anchored_clause20229 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 13] (by decide)
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

theorem es6Anchored_clause20230 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 14] (by decide)
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

theorem es6Anchored_clause20231 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 14] (by decide)
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

theorem es6Anchored_clause20232 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 15] (by decide)
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

theorem es6Anchored_clause20233 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 11, 16] (by decide)
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

theorem es6Anchored_clause20234 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 13] (by decide)
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

theorem es6Anchored_clause20235 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 13] (by decide)
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

theorem es6Anchored_clause20236 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 13] (by decide)
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

theorem es6Anchored_clause20237 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 14] (by decide)
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

theorem es6Anchored_clause20238 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 14] (by decide)
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

theorem es6Anchored_clause20239 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 15] (by decide)
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

theorem es6Anchored_clause20240 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 15] (by decide)
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

theorem es6Anchored_clause20241 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 16] (by decide)
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

theorem es6Anchored_clause20242 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 12, 16] (by decide)
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

theorem es6Anchored_clause20243 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 13, 14] (by decide)
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

theorem es6Anchored_clause20244 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 13, 15] (by decide)
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

theorem es6Anchored_clause20245 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 13, 16] (by decide)
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

theorem es6Anchored_clause20246 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 14, 15] (by decide)
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

theorem es6Anchored_clause20247 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 14, 16] (by decide)
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

theorem es6Anchored_clause20248 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 5, 15, 16] (by decide)
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

theorem es6Anchored_clause20249 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20250 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20251 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20252 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20253 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20254 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20255 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20256 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20257 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20258 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20259 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 8] (by decide)
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

theorem es6Anchored_clause20260 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20261 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20262 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20263 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20264 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20265 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20266 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20267 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20268 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20269 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20270 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20271 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 9] (by decide)
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

theorem es6Anchored_clause20272 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20273 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20274 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20275 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20276 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20277 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20278 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20279 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20280 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20281 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20282 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 10] (by decide)
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

theorem es6Anchored_clause20283 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20284 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20285 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20286 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20287 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20288 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20289 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20290 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20291 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20292 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 11] (by decide)
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

theorem es6Anchored_clause20293 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 12] (by decide)
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

theorem es6Anchored_clause20294 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 12] (by decide)
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

theorem es6Anchored_clause20295 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 12] (by decide)
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

theorem es6Anchored_clause20296 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 12] (by decide)
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

theorem es6Anchored_clause20297 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 12] (by decide)
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

theorem es6Anchored_clause20298 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 12] (by decide)
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

theorem es6Anchored_clause20299 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause20300 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause20301 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause20302 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause20303 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause20304 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause20305 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause20306 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 15] (by decide)
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

theorem es6Anchored_clause20307 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 7, 16] (by decide)
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

theorem es6Anchored_clause20308 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20309 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20310 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20311 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20312 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20313 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20314 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20315 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20316 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20317 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20318 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause20319 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20320 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20321 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20322 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20323 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20324 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20325 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20326 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20327 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20328 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20329 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause20330 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20331 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20332 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20333 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20334 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20335 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20336 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20337 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20338 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20339 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause20340 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause20341 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause20342 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause20343 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause20344 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause20345 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause20346 (chi : TripleColoring 17)
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
      ¬(chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause20347 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause20348 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause20349 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause20350 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause20351 (chi : TripleColoring 17)
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
      (chi ⟨1, 2, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 2, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨2, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 2, 4, 6, 8, 14] (by decide)
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
