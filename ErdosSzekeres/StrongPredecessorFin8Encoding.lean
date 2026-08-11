module

public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace ErdosSzekeres

def StrongPredecessorFin8Quad (χ : TripleColoring 8) (a b c d : Fin 8)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    χ ⟨a, c, d, hab.trans hbc, hcd⟩ = χ ⟨b, c, d, hbc, hcd⟩

theorem strongPredecessorFin8Quad_iff_strongSet (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrongPredecessorFin8Quad χ a b c d hab hbc hcd ↔
      IsStrongPolygonSet χ {a, b, c, d} := by
  constructor
  · rintro ⟨h₁, h₂⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl <;> try omega
    exact ⟨h₁, h₂⟩
  · intro h
    exact h hab hbc hcd (by simp) (by simp) (by simp) (by simp)

theorem strongPredecessorFin8Quad_iff_left (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrongPredecessorFin8Quad χ a b c d hab hbc hcd ↔
      (((χ ⟨a, b, c, hab, hbc⟩ = Turn.left) ↔
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩ = Turn.left)) ∧
       ((χ ⟨a, c, d, hab.trans hbc, hcd⟩ = Turn.left) ↔
        (χ ⟨b, c, d, hbc, hcd⟩ = Turn.left))) := by
  unfold StrongPredecessorFin8Quad
  generalize h₀ : χ ⟨a, b, c, hab, hbc⟩ = x₀
  generalize h₁ : χ ⟨a, b, d, hab, hbc.trans hcd⟩ = x₁
  generalize h₂ : χ ⟨a, c, d, hab.trans hbc, hcd⟩ = x₂
  generalize h₃ : χ ⟨b, c, d, hbc, hcd⟩ = x₃
  cases x₀ <;> cases x₁ <;> cases x₂ <;> cases x₃ <;> simp

theorem strongPredecessorFin8_notStrongFive_quads (χ : TripleColoring 8)
    (a b c d e : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hnot : ¬ IsStrongPolygonSet χ {a, b, c, d, e}) :
    ¬ StrongPredecessorFin8Quad χ a b c d hab hbc hcd ∨
    ¬ StrongPredecessorFin8Quad χ a b c e hab hbc (hcd.trans hde) ∨
    ¬ StrongPredecessorFin8Quad χ a b d e hab (hbc.trans hcd) hde ∨
    ¬ StrongPredecessorFin8Quad χ a c d e (hab.trans hbc) hcd hde ∨
    ¬ StrongPredecessorFin8Quad χ b c d e hbc hcd hde := by
  by_contra h
  push Not at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄⟩
  apply hnot
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals simp_all [StrongPredecessorFin8Quad]

theorem strongPredecessorFin8_containsFour_iff (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ContainsStrongPolygonSet χ {a, b, c, d} 4 ↔
      StrongPredecessorFin8Quad χ a b c d hab hbc hcd := by
  rw [strongPredecessorFin8Quad_iff_strongSet]
  constructor
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    have heq : polygon = {a, b, c, d} := by
      apply Finset.eq_of_subset_of_card_le hsub
      simp [hcard, hab.ne, (hab.trans hbc).ne, (hab.trans (hbc.trans hcd)).ne,
        hbc.ne, (hbc.trans hcd).ne, hcd.ne]
    simpa [heq] using hstrong
  · intro h
    exact ⟨{a, b, c, d}, by simp, by simp [hab.ne, (hab.trans hbc).ne,
      (hab.trans (hbc.trans hcd)).ne, hbc.ne, (hbc.trans hcd).ne, hcd.ne], h⟩

theorem strongPredecessorFin8_notContainsFour_iff (χ : TripleColoring 8)
    (a b c d : Fin 8) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ¬ ContainsStrongPolygonSet χ {a, b, c, d} 4 ↔
      ¬ StrongPredecessorFin8Quad χ a b c d hab hbc hcd :=
  not_congr (strongPredecessorFin8_containsFour_iff χ a b c d hab hbc hcd)


/-- Opaque names keep LRAT atom substitution linear in the certificate bridge. -/
def StrongPredecessorFin8Atom001 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 1, 2, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom002 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 1, 3, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom003 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 1, 4, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom004 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 1, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom005 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 1, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom006 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 1, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom007 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 2, 3, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom008 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 2, 4, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom009 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 2, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom010 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 2, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom011 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 2, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom012 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 3, 4, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom013 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 3, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom014 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 3, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom015 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 3, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom016 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 4, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom017 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 4, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom018 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 4, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom019 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 5, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom020 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 5, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom021 (χ : TripleColoring 8) : Prop :=
  (χ ⟨0, 6, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom022 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 2, 3, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom023 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 2, 4, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom024 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 2, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom025 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 2, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom026 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 2, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom027 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 3, 4, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom028 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 3, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom029 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 3, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom030 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 3, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom031 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 4, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom032 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 4, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom033 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 4, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom034 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 5, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom035 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 5, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom036 (χ : TripleColoring 8) : Prop :=
  (χ ⟨1, 6, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom037 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 3, 4, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom038 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 3, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom039 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 3, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom040 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 3, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom041 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 4, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom042 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 4, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom043 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 4, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom044 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 5, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom045 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 5, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom046 (χ : TripleColoring 8) : Prop :=
  (χ ⟨2, 6, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom047 (χ : TripleColoring 8) : Prop :=
  (χ ⟨3, 4, 5, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom048 (χ : TripleColoring 8) : Prop :=
  (χ ⟨3, 4, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom049 (χ : TripleColoring 8) : Prop :=
  (χ ⟨3, 4, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom050 (χ : TripleColoring 8) : Prop :=
  (χ ⟨3, 5, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom051 (χ : TripleColoring 8) : Prop :=
  (χ ⟨3, 5, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom052 (χ : TripleColoring 8) : Prop :=
  (χ ⟨3, 6, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom053 (χ : TripleColoring 8) : Prop :=
  (χ ⟨4, 5, 6, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom054 (χ : TripleColoring 8) : Prop :=
  (χ ⟨4, 5, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom055 (χ : TripleColoring 8) : Prop :=
  (χ ⟨4, 6, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom056 (χ : TripleColoring 8) : Prop :=
  (χ ⟨5, 6, 7, by decide, by decide⟩ = Turn.left)

def StrongPredecessorFin8Atom057 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 2 3 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom058 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 2 4 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom059 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 2 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom060 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 2 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom061 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 2 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom062 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 3 4 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom063 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 3 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom064 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 3 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom065 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 3 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom066 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 4 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom067 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 4 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom068 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 4 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom069 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom070 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom071 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 1 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom072 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 3 4 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom073 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 3 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom074 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 3 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom075 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 3 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom076 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 4 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom077 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 4 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom078 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 4 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom079 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom080 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom081 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 2 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom082 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 3 4 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom083 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 3 4 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom084 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 3 4 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom085 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 3 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom086 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 3 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom087 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 3 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom088 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 4 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom089 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 4 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom090 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 4 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom091 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 0 5 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom092 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 3 4 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom093 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 3 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom094 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 3 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom095 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 3 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom096 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 4 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom097 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 4 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom098 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 4 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom099 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom100 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom101 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 2 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom102 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 3 4 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom103 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 3 4 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom104 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 3 4 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom105 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 3 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom106 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 3 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom107 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 3 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom108 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 4 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom109 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 4 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom110 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 4 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom111 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 1 5 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom112 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 3 4 5 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom113 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 3 4 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom114 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 3 4 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom115 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 3 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom116 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 3 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom117 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 3 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom118 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 4 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom119 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 4 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom120 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 4 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom121 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 2 5 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom122 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 3 4 5 6 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom123 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 3 4 5 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom124 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 3 4 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom125 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 3 5 6 7 (by decide) (by decide) (by decide))

def StrongPredecessorFin8Atom126 (χ : TripleColoring 8) : Prop :=
  (StrongPredecessorFin8Quad χ 4 5 6 7 (by decide) (by decide) (by decide))

end ErdosSzekeres

end
