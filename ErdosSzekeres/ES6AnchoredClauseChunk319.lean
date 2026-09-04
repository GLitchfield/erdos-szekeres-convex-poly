module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 319. -/

theorem es6Anchored_clause40832 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 5, 12, 13, 14, 16] (by decide)
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

theorem es6Anchored_clause40833 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 5, 12, 13, 15, 16] (by decide)
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

theorem es6Anchored_clause40834 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 5, 12, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause40835 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨12, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 5, 12, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause40836 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 5, 13, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause40837 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨13, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨14, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 5, 13, 14, 15, 16] (by decide)
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

theorem es6Anchored_clause40838 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40839 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40840 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40841 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40842 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40843 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40844 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40845 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40846 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40847 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40848 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40849 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40850 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 10] (by decide)
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

theorem es6Anchored_clause40851 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40852 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40853 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40854 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40855 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40856 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40857 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40858 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40859 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40860 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40861 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 11] (by decide)
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

theorem es6Anchored_clause40862 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40863 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40864 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40865 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40866 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40867 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40868 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40869 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40870 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40871 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40872 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 12] (by decide)
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

theorem es6Anchored_clause40873 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40874 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40875 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40876 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40877 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40878 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40879 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40880 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40881 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40882 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40883 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 13] (by decide)
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

theorem es6Anchored_clause40884 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40885 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40886 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40887 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40888 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40889 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40890 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40891 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40892 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40893 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40894 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 14] (by decide)
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

theorem es6Anchored_clause40895 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 15] (by decide)
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

theorem es6Anchored_clause40896 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 15] (by decide)
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

theorem es6Anchored_clause40897 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 15] (by decide)
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

theorem es6Anchored_clause40898 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 15] (by decide)
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

theorem es6Anchored_clause40899 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 15] (by decide)
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

theorem es6Anchored_clause40900 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 15] (by decide)
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

theorem es6Anchored_clause40901 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 15] (by decide)
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

theorem es6Anchored_clause40902 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 16] (by decide)
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

theorem es6Anchored_clause40903 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 16] (by decide)
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

theorem es6Anchored_clause40904 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 9, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 9, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 9, 16] (by decide)
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

theorem es6Anchored_clause40905 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40906 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40907 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40908 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40909 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40910 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40911 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40912 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40913 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40914 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40915 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40916 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 11] (by decide)
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

theorem es6Anchored_clause40917 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40918 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40919 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40920 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40921 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40922 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40923 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40924 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40925 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40926 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40927 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40928 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 12] (by decide)
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

theorem es6Anchored_clause40929 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40930 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40931 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40932 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40933 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40934 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40935 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40936 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40937 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40938 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40939 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40940 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 13] (by decide)
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

theorem es6Anchored_clause40941 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40942 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40943 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40944 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40945 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40946 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40947 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40948 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40949 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40950 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40951 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 14] (by decide)
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

theorem es6Anchored_clause40952 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

theorem es6Anchored_clause40953 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

theorem es6Anchored_clause40954 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

theorem es6Anchored_clause40955 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

theorem es6Anchored_clause40956 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

theorem es6Anchored_clause40957 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

theorem es6Anchored_clause40958 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

theorem es6Anchored_clause40959 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 10, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨8, 10, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 6, 7, 8, 10, 15] (by decide)
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

end ErdosSzekeres

end
