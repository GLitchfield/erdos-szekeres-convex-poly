module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 276. -/

theorem es6Anchored_clause35328 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35329 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35330 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35331 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35332 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35333 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35334 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35335 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35336 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 13] (by decide)
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

theorem es6Anchored_clause35337 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35338 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35339 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35340 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35341 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35342 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35343 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35344 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35345 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35346 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35347 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 14] (by decide)
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

theorem es6Anchored_clause35348 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 15] (by decide)
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

theorem es6Anchored_clause35349 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 15] (by decide)
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

theorem es6Anchored_clause35350 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 15] (by decide)
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

theorem es6Anchored_clause35351 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 15] (by decide)
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

theorem es6Anchored_clause35352 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 15] (by decide)
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

theorem es6Anchored_clause35353 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 15] (by decide)
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

theorem es6Anchored_clause35354 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 16] (by decide)
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

theorem es6Anchored_clause35355 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 16] (by decide)
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

theorem es6Anchored_clause35356 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 7, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 7, 16] (by decide)
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

theorem es6Anchored_clause35357 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35358 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35359 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35360 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35361 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35362 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35363 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35364 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35365 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35366 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35367 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 9] (by decide)
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

theorem es6Anchored_clause35368 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35369 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35370 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35371 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35372 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35373 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35374 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35375 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35376 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35377 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35378 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 10] (by decide)
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

theorem es6Anchored_clause35379 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35380 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35381 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35382 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35383 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35384 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35385 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35386 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35387 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35388 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35389 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 11] (by decide)
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

theorem es6Anchored_clause35390 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35391 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35392 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35393 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35394 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35395 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35396 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35397 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35398 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35399 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35400 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35401 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 12] (by decide)
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

theorem es6Anchored_clause35402 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35403 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35404 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35405 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35406 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35407 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35408 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35409 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35410 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35411 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35412 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35413 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 13] (by decide)
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

theorem es6Anchored_clause35414 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35415 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35416 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35417 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35418 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35419 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35420 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35421 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35422 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35423 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35424 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 14] (by decide)
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

theorem es6Anchored_clause35425 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 15] (by decide)
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

theorem es6Anchored_clause35426 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 15] (by decide)
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

theorem es6Anchored_clause35427 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 15] (by decide)
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

theorem es6Anchored_clause35428 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 15] (by decide)
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

theorem es6Anchored_clause35429 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 15] (by decide)
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

theorem es6Anchored_clause35430 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 15] (by decide)
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

theorem es6Anchored_clause35431 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 15] (by decide)
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

theorem es6Anchored_clause35432 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 16] (by decide)
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

theorem es6Anchored_clause35433 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 8, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 8, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 8, 16] (by decide)
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

theorem es6Anchored_clause35434 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35435 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35436 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35437 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35438 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35439 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35440 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35441 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35442 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35443 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35444 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 10] (by decide)
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

theorem es6Anchored_clause35445 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35446 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35447 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35448 (chi : TripleColoring 17)
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
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35449 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35450 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35451 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35452 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35453 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35454 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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

theorem es6Anchored_clause35455 (chi : TripleColoring 17)
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
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 9, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨6, 9, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![3, 4, 5, 6, 9, 11] (by decide)
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
