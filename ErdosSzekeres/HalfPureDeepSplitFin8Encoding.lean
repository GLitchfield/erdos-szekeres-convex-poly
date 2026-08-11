module

public import ErdosSzekeres.StrongPredecessorFin8Encoding

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false

namespace ErdosSzekeres

/-- The exact bounded conclusion certified by the Fin8 LRAT proof. -/
def HalfPureDeepSplitFin8Conclusion (χ : TripleColoring 8) : Prop :=
  ∃ lower upper : Finset (Fin 8),
    HasDeepBelowSplit χ lower upper ∧
    ((upper.Nonempty ∧ 8 ≤ 2 * lower.card ∧
        ∀ polygon : Finset (Fin 8),
          polygon ⊆ lower → polygon.card = 5 - 1 →
            IsStrongPolygonSet χ polygon → IsCupSet χ polygon) ∨
     (lower.Nonempty ∧ 8 ≤ 2 * upper.card ∧
        ∀ polygon : Finset (Fin 8),
          polygon ⊆ upper → polygon.card = 5 - 1 →
            IsStrongPolygonSet χ polygon → IsCapSet χ polygon))

theorem halfPureDeepSplitFin8_isCupSet_four_iff (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    IsCupSet χ {a, b, c, d} ↔
      χ ⟨a, b, c, hab, hbc⟩ = Turn.left ∧
      χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.left ∧
      χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.left ∧
      χ ⟨b, c, d, hbc, hcd⟩ = Turn.left := by
  constructor
  · intro h
    exact ⟨h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;> try omega

theorem halfPureDeepSplitFin8_isCapSet_four_iff (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    IsCapSet χ {a, b, c, d} ↔
      χ ⟨a, b, c, hab, hbc⟩ = Turn.right ∧
      χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.right ∧
      χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.right ∧
      χ ⟨b, c, d, hbc, hcd⟩ = Turn.right := by
  constructor
  · intro h
    exact ⟨h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp),
      h _ (by simp) (by simp) (by simp)⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩ ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;> try omega

def HalfPureDeepSplitFin8Atom001 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 1, 2, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom002 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 1, 3, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom003 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 1, 4, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom004 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 1, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom005 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 1, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom006 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 1, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom007 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom008 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 2, 4, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom009 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom010 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom011 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom012 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 3, 4, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom013 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom014 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom015 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom016 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 4, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom017 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 4, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom018 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 4, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom019 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom020 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom021 (χ : TripleColoring 8) : Prop :=
  χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom022 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 2, 3, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom023 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 2, 4, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom024 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 2, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom025 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 2, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom026 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 2, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom027 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 3, 4, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom028 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 3, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom029 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 3, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom030 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 3, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom031 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 4, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom032 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 4, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom033 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 4, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom034 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom035 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom036 (χ : TripleColoring 8) : Prop :=
  χ ⟨1, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom037 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom038 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom039 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom040 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom041 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom042 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom043 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom044 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom045 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom046 (χ : TripleColoring 8) : Prop :=
  χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom047 (χ : TripleColoring 8) : Prop :=
  χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom048 (χ : TripleColoring 8) : Prop :=
  χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom049 (χ : TripleColoring 8) : Prop :=
  χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom050 (χ : TripleColoring 8) : Prop :=
  χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom051 (χ : TripleColoring 8) : Prop :=
  χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom052 (χ : TripleColoring 8) : Prop :=
  χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom053 (χ : TripleColoring 8) : Prop :=
  χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom054 (χ : TripleColoring 8) : Prop :=
  χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom055 (χ : TripleColoring 8) : Prop :=
  χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom056 (χ : TripleColoring 8) : Prop :=
  χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left

def HalfPureDeepSplitFin8Atom057 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 3
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom058 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 4
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom059 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom060 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom061 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom062 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 4
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom063 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom064 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom065 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom066 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom067 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom068 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom069 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom070 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom071 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom072 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 4
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom073 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom074 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom075 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom076 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom077 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom078 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom079 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom080 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom081 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom082 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom083 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom084 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom085 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom086 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom087 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom088 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom089 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom090 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom091 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 5 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom092 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 4
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom093 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom094 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom095 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom096 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom097 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom098 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom099 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom100 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom101 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom102 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom103 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom104 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom105 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom106 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom107 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom108 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom109 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom110 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom111 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 5 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom112 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 5
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom113 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom114 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom115 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom116 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom117 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom118 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom119 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom120 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom121 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 5 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom122 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 5 6
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom123 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 5 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom124 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom125 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 5 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom126 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 4 5 6 7
    (by decide) (by decide) (by decide)

def HalfPureDeepSplitFin8Atom127 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 3
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 2, 3}

def HalfPureDeepSplitFin8Atom128 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 2, 4}

def HalfPureDeepSplitFin8Atom129 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 2, 5}

def HalfPureDeepSplitFin8Atom130 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 2, 6}

def HalfPureDeepSplitFin8Atom131 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 2, 7}

def HalfPureDeepSplitFin8Atom132 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 3, 4}

def HalfPureDeepSplitFin8Atom133 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 3, 5}

def HalfPureDeepSplitFin8Atom134 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 3, 6}

def HalfPureDeepSplitFin8Atom135 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 3, 7}

def HalfPureDeepSplitFin8Atom136 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 4, 5}

def HalfPureDeepSplitFin8Atom137 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 4, 6}

def HalfPureDeepSplitFin8Atom138 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 4, 7}

def HalfPureDeepSplitFin8Atom139 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 5, 6}

def HalfPureDeepSplitFin8Atom140 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 5, 7}

def HalfPureDeepSplitFin8Atom141 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 1, 6, 7}

def HalfPureDeepSplitFin8Atom142 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 3, 4}

def HalfPureDeepSplitFin8Atom143 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 3, 5}

def HalfPureDeepSplitFin8Atom144 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 3, 6}

def HalfPureDeepSplitFin8Atom145 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 3, 7}

def HalfPureDeepSplitFin8Atom146 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 4, 5}

def HalfPureDeepSplitFin8Atom147 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 4, 6}

def HalfPureDeepSplitFin8Atom148 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 4, 7}

def HalfPureDeepSplitFin8Atom149 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 5, 6}

def HalfPureDeepSplitFin8Atom150 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 5, 7}

def HalfPureDeepSplitFin8Atom151 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 2, 6, 7}

def HalfPureDeepSplitFin8Atom152 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 3, 4, 5}

def HalfPureDeepSplitFin8Atom153 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 3, 4, 6}

def HalfPureDeepSplitFin8Atom154 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 3, 4, 7}

def HalfPureDeepSplitFin8Atom155 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 3, 5, 6}

def HalfPureDeepSplitFin8Atom156 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 3, 5, 7}

def HalfPureDeepSplitFin8Atom157 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 3, 6, 7}

def HalfPureDeepSplitFin8Atom158 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 4, 5, 6}

def HalfPureDeepSplitFin8Atom159 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 4, 5, 7}

def HalfPureDeepSplitFin8Atom160 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 4, 6, 7}

def HalfPureDeepSplitFin8Atom161 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {0, 5, 6, 7}

def HalfPureDeepSplitFin8Atom162 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 3, 4}

def HalfPureDeepSplitFin8Atom163 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 3, 5}

def HalfPureDeepSplitFin8Atom164 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 3, 6}

def HalfPureDeepSplitFin8Atom165 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 3, 7}

def HalfPureDeepSplitFin8Atom166 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 4, 5}

def HalfPureDeepSplitFin8Atom167 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 4, 6}

def HalfPureDeepSplitFin8Atom168 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 4, 7}

def HalfPureDeepSplitFin8Atom169 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 5, 6}

def HalfPureDeepSplitFin8Atom170 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 5, 7}

def HalfPureDeepSplitFin8Atom171 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 2, 6, 7}

def HalfPureDeepSplitFin8Atom172 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 3, 4, 5}

def HalfPureDeepSplitFin8Atom173 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 3, 4, 6}

def HalfPureDeepSplitFin8Atom174 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 3, 4, 7}

def HalfPureDeepSplitFin8Atom175 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 3, 5, 6}

def HalfPureDeepSplitFin8Atom176 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 3, 5, 7}

def HalfPureDeepSplitFin8Atom177 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 3, 6, 7}

def HalfPureDeepSplitFin8Atom178 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 4, 5, 6}

def HalfPureDeepSplitFin8Atom179 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 4, 5, 7}

def HalfPureDeepSplitFin8Atom180 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 4, 6, 7}

def HalfPureDeepSplitFin8Atom181 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {1, 5, 6, 7}

def HalfPureDeepSplitFin8Atom182 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 3, 4, 5}

def HalfPureDeepSplitFin8Atom183 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 3, 4, 6}

def HalfPureDeepSplitFin8Atom184 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 3, 4, 7}

def HalfPureDeepSplitFin8Atom185 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 3, 5, 6}

def HalfPureDeepSplitFin8Atom186 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 3, 5, 7}

def HalfPureDeepSplitFin8Atom187 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 3, 6, 7}

def HalfPureDeepSplitFin8Atom188 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 4, 5, 6}

def HalfPureDeepSplitFin8Atom189 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 4, 5, 7}

def HalfPureDeepSplitFin8Atom190 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 4, 6, 7}

def HalfPureDeepSplitFin8Atom191 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {2, 5, 6, 7}

def HalfPureDeepSplitFin8Atom192 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {3, 4, 5, 6}

def HalfPureDeepSplitFin8Atom193 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {3, 4, 5, 7}

def HalfPureDeepSplitFin8Atom194 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {3, 4, 6, 7}

def HalfPureDeepSplitFin8Atom195 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {3, 5, 6, 7}

def HalfPureDeepSplitFin8Atom196 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 4 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCupSet χ {4, 5, 6, 7}

def HalfPureDeepSplitFin8Atom197 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 3
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 2, 3}

def HalfPureDeepSplitFin8Atom198 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 2, 4}

def HalfPureDeepSplitFin8Atom199 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 2, 5}

def HalfPureDeepSplitFin8Atom200 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 2, 6}

def HalfPureDeepSplitFin8Atom201 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 2 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 2, 7}

def HalfPureDeepSplitFin8Atom202 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 3, 4}

def HalfPureDeepSplitFin8Atom203 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 3, 5}

def HalfPureDeepSplitFin8Atom204 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 3, 6}

def HalfPureDeepSplitFin8Atom205 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 3 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 3, 7}

def HalfPureDeepSplitFin8Atom206 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 4, 5}

def HalfPureDeepSplitFin8Atom207 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 4, 6}

def HalfPureDeepSplitFin8Atom208 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 4, 7}

def HalfPureDeepSplitFin8Atom209 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 5, 6}

def HalfPureDeepSplitFin8Atom210 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 5, 7}

def HalfPureDeepSplitFin8Atom211 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 1 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 1, 6, 7}

def HalfPureDeepSplitFin8Atom212 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 3, 4}

def HalfPureDeepSplitFin8Atom213 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 3, 5}

def HalfPureDeepSplitFin8Atom214 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 3, 6}

def HalfPureDeepSplitFin8Atom215 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 3 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 3, 7}

def HalfPureDeepSplitFin8Atom216 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 4, 5}

def HalfPureDeepSplitFin8Atom217 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 4, 6}

def HalfPureDeepSplitFin8Atom218 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 4, 7}

def HalfPureDeepSplitFin8Atom219 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 5, 6}

def HalfPureDeepSplitFin8Atom220 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 5, 7}

def HalfPureDeepSplitFin8Atom221 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 2 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 2, 6, 7}

def HalfPureDeepSplitFin8Atom222 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 3, 4, 5}

def HalfPureDeepSplitFin8Atom223 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 3, 4, 6}

def HalfPureDeepSplitFin8Atom224 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 3, 4, 7}

def HalfPureDeepSplitFin8Atom225 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 3, 5, 6}

def HalfPureDeepSplitFin8Atom226 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 3, 5, 7}

def HalfPureDeepSplitFin8Atom227 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 3 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 3, 6, 7}

def HalfPureDeepSplitFin8Atom228 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 4, 5, 6}

def HalfPureDeepSplitFin8Atom229 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 4, 5, 7}

def HalfPureDeepSplitFin8Atom230 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 4, 6, 7}

def HalfPureDeepSplitFin8Atom231 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 0 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {0, 5, 6, 7}

def HalfPureDeepSplitFin8Atom232 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 4
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 3, 4}

def HalfPureDeepSplitFin8Atom233 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 3, 5}

def HalfPureDeepSplitFin8Atom234 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 3, 6}

def HalfPureDeepSplitFin8Atom235 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 3 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 3, 7}

def HalfPureDeepSplitFin8Atom236 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 4, 5}

def HalfPureDeepSplitFin8Atom237 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 4, 6}

def HalfPureDeepSplitFin8Atom238 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 4, 7}

def HalfPureDeepSplitFin8Atom239 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 5, 6}

def HalfPureDeepSplitFin8Atom240 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 5, 7}

def HalfPureDeepSplitFin8Atom241 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 2 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 2, 6, 7}

def HalfPureDeepSplitFin8Atom242 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 3, 4, 5}

def HalfPureDeepSplitFin8Atom243 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 3, 4, 6}

def HalfPureDeepSplitFin8Atom244 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 3, 4, 7}

def HalfPureDeepSplitFin8Atom245 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 3, 5, 6}

def HalfPureDeepSplitFin8Atom246 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 3, 5, 7}

def HalfPureDeepSplitFin8Atom247 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 3 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 3, 6, 7}

def HalfPureDeepSplitFin8Atom248 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 4, 5, 6}

def HalfPureDeepSplitFin8Atom249 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 4, 5, 7}

def HalfPureDeepSplitFin8Atom250 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 4, 6, 7}

def HalfPureDeepSplitFin8Atom251 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 1 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {1, 5, 6, 7}

def HalfPureDeepSplitFin8Atom252 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 5
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 3, 4, 5}

def HalfPureDeepSplitFin8Atom253 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 3, 4, 6}

def HalfPureDeepSplitFin8Atom254 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 4 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 3, 4, 7}

def HalfPureDeepSplitFin8Atom255 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 3, 5, 6}

def HalfPureDeepSplitFin8Atom256 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 3, 5, 7}

def HalfPureDeepSplitFin8Atom257 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 3 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 3, 6, 7}

def HalfPureDeepSplitFin8Atom258 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 4, 5, 6}

def HalfPureDeepSplitFin8Atom259 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 4, 5, 7}

def HalfPureDeepSplitFin8Atom260 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 4, 6, 7}

def HalfPureDeepSplitFin8Atom261 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 2 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {2, 5, 6, 7}

def HalfPureDeepSplitFin8Atom262 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 5 6
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {3, 4, 5, 6}

def HalfPureDeepSplitFin8Atom263 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 5 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {3, 4, 5, 7}

def HalfPureDeepSplitFin8Atom264 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 4 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {3, 4, 6, 7}

def HalfPureDeepSplitFin8Atom265 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 3 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {3, 5, 6, 7}

def HalfPureDeepSplitFin8Atom266 (χ : TripleColoring 8) : Prop :=
  StrongPredecessorFin8Quad χ 4 5 6 7
      (by decide) (by decide) (by decide) ∧
    ¬IsCapSet χ {4, 5, 6, 7}

theorem halfPureDeepSplitFin8_fourSubset_eq_mask030 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 3, 4} →
      polygon.card = 4 → polygon = {1, 2, 3, 4} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask046 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 3, 5} →
      polygon.card = 4 → polygon = {1, 2, 3, 5} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask054 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 4, 5} →
      polygon.card = 4 → polygon = {1, 2, 4, 5} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask058 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 3, 4, 5} →
      polygon.card = 4 → polygon = {1, 3, 4, 5} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask060 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 3, 4, 5} →
      polygon.card = 4 → polygon = {2, 3, 4, 5} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask078 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 3, 6} →
      polygon.card = 4 → polygon = {1, 2, 3, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask086 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 4, 6} →
      polygon.card = 4 → polygon = {1, 2, 4, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask090 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 3, 4, 6} →
      polygon.card = 4 → polygon = {1, 3, 4, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask092 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 3, 4, 6} →
      polygon.card = 4 → polygon = {2, 3, 4, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask102 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 5, 6} →
      polygon.card = 4 → polygon = {1, 2, 5, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask106 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 3, 5, 6} →
      polygon.card = 4 → polygon = {1, 3, 5, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask108 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 3, 5, 6} →
      polygon.card = 4 → polygon = {2, 3, 5, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask114 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 4, 5, 6} →
      polygon.card = 4 → polygon = {1, 4, 5, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask116 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 4, 5, 6} →
      polygon.card = 4 → polygon = {2, 4, 5, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask120 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {3, 4, 5, 6} →
      polygon.card = 4 → polygon = {3, 4, 5, 6} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask150 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 4, 7} →
      polygon.card = 4 → polygon = {1, 2, 4, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask154 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 3, 4, 7} →
      polygon.card = 4 → polygon = {1, 3, 4, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask156 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 3, 4, 7} →
      polygon.card = 4 → polygon = {2, 3, 4, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask170 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 3, 5, 7} →
      polygon.card = 4 → polygon = {1, 3, 5, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask172 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 3, 5, 7} →
      polygon.card = 4 → polygon = {2, 3, 5, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask178 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 4, 5, 7} →
      polygon.card = 4 → polygon = {1, 4, 5, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask180 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 4, 5, 7} →
      polygon.card = 4 → polygon = {2, 4, 5, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask184 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {3, 4, 5, 7} →
      polygon.card = 4 → polygon = {3, 4, 5, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask198 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 2, 6, 7} →
      polygon.card = 4 → polygon = {1, 2, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask202 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 3, 6, 7} →
      polygon.card = 4 → polygon = {1, 3, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask204 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 3, 6, 7} →
      polygon.card = 4 → polygon = {2, 3, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask210 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 4, 6, 7} →
      polygon.card = 4 → polygon = {1, 4, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask212 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 4, 6, 7} →
      polygon.card = 4 → polygon = {2, 4, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask216 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {3, 4, 6, 7} →
      polygon.card = 4 → polygon = {3, 4, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask226 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {1, 5, 6, 7} →
      polygon.card = 4 → polygon = {1, 5, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask228 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {2, 5, 6, 7} →
      polygon.card = 4 → polygon = {2, 5, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask232 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {3, 5, 6, 7} →
      polygon.card = 4 → polygon = {3, 5, 6, 7} := by decide

theorem halfPureDeepSplitFin8_fourSubset_eq_mask240 :
    ∀ polygon : Finset (Fin 8), polygon ⊆ {4, 5, 6, 7} →
      polygon.card = 4 → polygon = {4, 5, 6, 7} := by decide

end ErdosSzekeres

end
