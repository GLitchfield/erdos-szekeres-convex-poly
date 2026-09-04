module

public import ErdosSzekeres.ES6AnchoredEncoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-! Retained anchored ES(6) semantic clauses, group 171. -/

theorem es6Anchored_clause21888 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 8] (by decide)
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

theorem es6Anchored_clause21889 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 8] (by decide)
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

theorem es6Anchored_clause21890 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 8] (by decide)
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

theorem es6Anchored_clause21891 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 8] (by decide)
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

theorem es6Anchored_clause21892 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 8] (by decide)
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

theorem es6Anchored_clause21893 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 8] (by decide)
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

theorem es6Anchored_clause21894 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 8] (by decide)
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

theorem es6Anchored_clause21895 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21896 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21897 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21898 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21899 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21900 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21901 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21902 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21903 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21904 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21905 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 9] (by decide)
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

theorem es6Anchored_clause21906 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21907 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21908 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21909 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21910 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21911 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21912 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21913 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21914 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21915 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21916 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 10] (by decide)
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

theorem es6Anchored_clause21917 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21918 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21919 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21920 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21921 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21922 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21923 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21924 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21925 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21926 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21927 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21928 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 11] (by decide)
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

theorem es6Anchored_clause21929 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21930 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21931 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21932 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21933 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21934 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21935 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21936 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21937 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21938 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21939 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 12] (by decide)
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

theorem es6Anchored_clause21940 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21941 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21942 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21943 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21944 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21945 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21946 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21947 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 13] (by decide)
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

theorem es6Anchored_clause21948 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 14] (by decide)
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

theorem es6Anchored_clause21949 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 14] (by decide)
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

theorem es6Anchored_clause21950 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 15] (by decide)
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

theorem es6Anchored_clause21951 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 15] (by decide)
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

theorem es6Anchored_clause21952 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 6, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 6, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 6, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 6, 16] (by decide)
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

theorem es6Anchored_clause21953 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21954 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21955 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21956 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21957 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21958 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21959 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21960 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21961 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21962 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21963 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 8, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 8, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 8] (by decide)
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

theorem es6Anchored_clause21964 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21965 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21966 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21967 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21968 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21969 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21970 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21971 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21972 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21973 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21974 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 9, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 9, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 9] (by decide)
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

theorem es6Anchored_clause21975 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21976 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21977 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21978 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21979 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21980 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21981 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21982 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21983 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21984 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21985 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 10, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 10, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 10] (by decide)
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

theorem es6Anchored_clause21986 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21987 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21988 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21989 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21990 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21991 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21992 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21993 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21994 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21995 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21996 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 11, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 11, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 11] (by decide)
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

theorem es6Anchored_clause21997 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause21998 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause21999 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22000 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22001 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22002 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22003 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22004 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22005 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22006 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 12, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 12, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 12] (by decide)
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

theorem es6Anchored_clause22007 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 13] (by decide)
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

theorem es6Anchored_clause22008 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 13] (by decide)
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

theorem es6Anchored_clause22009 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 13] (by decide)
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

theorem es6Anchored_clause22010 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 13] (by decide)
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

theorem es6Anchored_clause22011 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 13] (by decide)
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

theorem es6Anchored_clause22012 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 13, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 13, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 13] (by decide)
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

theorem es6Anchored_clause22013 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 14, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 14, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 14] (by decide)
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

theorem es6Anchored_clause22014 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬((chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 3, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 15, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 15, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 15] (by decide)
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

theorem es6Anchored_clause22015 (chi : TripleColoring 17)
    (hallowed : ∀ (a b c d : Fin 17),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (chi ⟨a, b, c, hab, hbc⟩)
        (chi ⟨a, b, d, hab, hbc.trans hcd⟩)
        (chi ⟨a, c, d, hab.trans hbc, hcd⟩)
        (chi ⟨b, c, d, hbc, hcd⟩))
    (hno : ∀ f : Fin 6 ↪o Fin 17, ¬ IsStrongPolygonOn chi f)
    (hanchor : chi.IsAnchored) :
    ¬(¬(chi ⟨1, 3, 4, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 5, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 7, by decide, by decide⟩ = Turn.left) ∧
      ¬(chi ⟨1, 3, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨1, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 5, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 4, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨3, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 7, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 5, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨4, 7, 16, by decide, by decide⟩ = Turn.left) ∧
      (chi ⟨5, 7, 16, by decide, by decide⟩ = Turn.left)) := by
  intro hbad
  let f : Fin 6 ↪o Fin 17 := OrderEmbedding.ofStrictMono ![1, 3, 4, 5, 7, 16] (by decide)
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

end ErdosSzekeres

end
