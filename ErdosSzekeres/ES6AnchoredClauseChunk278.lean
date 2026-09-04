module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 278. -/

theorem es6Anchored_clause35584 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 11, 15] (by decide)
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

theorem es6Anchored_clause35585 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 11, 15] (by decide)
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

theorem es6Anchored_clause35586 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 11, 15] (by decide)
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

theorem es6Anchored_clause35587 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 11, 16] (by decide)
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

theorem es6Anchored_clause35588 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 11, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 11, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 11, 16] (by decide)
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

theorem es6Anchored_clause35589 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35590 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35591 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35592 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35593 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35594 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35595 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35596 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35597 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35598 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35599 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 13] (by decide)
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

theorem es6Anchored_clause35600 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35601 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35602 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35603 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35604 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35605 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35606 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35607 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35608 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35609 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 14] (by decide)
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

theorem es6Anchored_clause35610 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 15] (by decide)
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

theorem es6Anchored_clause35611 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 15] (by decide)
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

theorem es6Anchored_clause35612 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 15] (by decide)
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

theorem es6Anchored_clause35613 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 15] (by decide)
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

theorem es6Anchored_clause35614 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 15] (by decide)
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

theorem es6Anchored_clause35615 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 15] (by decide)
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

theorem es6Anchored_clause35616 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 15] (by decide)
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

theorem es6Anchored_clause35617 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 16] (by decide)
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

theorem es6Anchored_clause35618 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 12, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 12, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 12, 16] (by decide)
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

theorem es6Anchored_clause35619 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35620 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35621 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35622 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35623 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35624 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35625 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35626 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35627 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35628 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35629 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 14] (by decide)
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

theorem es6Anchored_clause35630 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 15] (by decide)
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

theorem es6Anchored_clause35631 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 15] (by decide)
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

theorem es6Anchored_clause35632 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 15] (by decide)
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

theorem es6Anchored_clause35633 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 15] (by decide)
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

theorem es6Anchored_clause35634 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 16] (by decide)
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

theorem es6Anchored_clause35635 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 13, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 13, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 13, 16] (by decide)
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

theorem es6Anchored_clause35636 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 15] (by decide)
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

theorem es6Anchored_clause35637 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 15] (by decide)
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

theorem es6Anchored_clause35638 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 15] (by decide)
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

theorem es6Anchored_clause35639 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 15] (by decide)
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

theorem es6Anchored_clause35640 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 15] (by decide)
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

theorem es6Anchored_clause35641 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 15] (by decide)
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

theorem es6Anchored_clause35642 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 16] (by decide)
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

theorem es6Anchored_clause35643 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 14, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 14, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 14, 16] (by decide)
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

theorem es6Anchored_clause35644 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 15, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 15, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 15, 16] (by decide)
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

theorem es6Anchored_clause35645 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35646 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35647 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35648 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35649 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35650 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35651 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35652 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35653 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35654 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35655 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 9] (by decide)
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

theorem es6Anchored_clause35656 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35657 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35658 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35659 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35660 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35661 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35662 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35663 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35664 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35665 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35666 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 10] (by decide)
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

theorem es6Anchored_clause35667 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35668 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35669 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35670 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35671 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35672 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35673 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35674 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35675 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35676 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35677 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 11] (by decide)
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

theorem es6Anchored_clause35678 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35679 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35680 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35681 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35682 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35683 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35684 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35685 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35686 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35687 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35688 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35689 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35690 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 12] (by decide)
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

theorem es6Anchored_clause35691 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35692 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35693 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35694 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35695 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35696 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35697 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35698 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35699 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35700 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35701 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 13] (by decide)
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

theorem es6Anchored_clause35702 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35703 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35704 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35705 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35706 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35707 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35708 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35709 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35710 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

theorem es6Anchored_clause35711 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨7, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 7, 8, 14] (by decide)
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

end ErdosSzekeres

end
