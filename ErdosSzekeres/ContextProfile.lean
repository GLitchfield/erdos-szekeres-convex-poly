module

public import ErdosSzekeres.Decomposable

@[expose] public section

/-!
# Fixed-ambient endpoint context profiles

This file introduces the fixed-ambient sweep-gap vocabulary used to state
endpoint-context invariants.  Restricting a vertex set does not relabel the
ambient `Fin n`, so the same gap and the same chain witness remain available.
-/

namespace ErdosSzekeres

noncomputable section

/-- A cut in the fixed ambient order on `Fin n`; `g` lies before vertex `g`. -/
abbrev SweepGap (n : ℕ) := Fin (n + 1)

/-- The external anchor at `g` lies weakly left of every vertex of `chain`. -/
def IsRightOfSweepGap {n : ℕ} (g : SweepGap n) (chain : Finset (Fin n)) : Prop :=
  ∀ x ∈ chain, g.val ≤ x.val

/-- The external anchor at `g` lies strictly right of every vertex of `chain`. -/
def IsLeftOfSweepGap {n : ℕ} (g : SweepGap n) (chain : Finset (Fin n)) : Prop :=
  ∀ x ∈ chain, x.val < g.val

/-- The chain has vertices strictly on both sides of the external anchor. -/
def StrictlyStraddlesSweepGap {n : ℕ} (g : SweepGap n)
    (chain : Finset (Fin n)) : Prop :=
  (∃ x ∈ chain, x.val < g.val) ∧ ∃ y ∈ chain, g.val ≤ y.val

/-- The three directional relations between a chain and an external anchor. -/
inductive SweepGapRelation where
  | anchorLeft
  | anchorRight
  | straddled
  deriving DecidableEq, Repr

/-- Interpret a directional relation without changing the fixed ambient order. -/
def HasSweepGapRelation {n : ℕ} (g : SweepGap n) (chain : Finset (Fin n)) :
    SweepGapRelation → Prop
  | .anchorLeft => IsRightOfSweepGap g chain
  | .anchorRight => IsLeftOfSweepGap g chain
  | .straddled => StrictlyStraddlesSweepGap g chain

/-- An `r`-cup in `s` carrying a specified fixed-ambient anchor relation. -/
def ContainsCupSetAtGap {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n))
    (r : ℕ) (g : SweepGap n) (relation : SweepGapRelation) : Prop :=
  ∃ cup : Finset (Fin n), cup ⊆ s ∧ cup.card = r ∧ IsCupSet χ cup ∧
    HasSweepGapRelation g cup relation

/-- An `r`-cap in `s` carrying a specified fixed-ambient anchor relation. -/
def ContainsCapSetAtGap {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n))
    (r : ℕ) (g : SweepGap n) (relation : SweepGapRelation) : Prop :=
  ∃ cap : Finset (Fin n), cap ⊆ s ∧ cap.card = r ∧ IsCapSet χ cap ∧
    HasSweepGapRelation g cap relation

namespace FinsetPolygon

variable {n r : ℕ} {χ : TripleColoring n} {s t : Finset (Fin n)}
  {g : SweepGap n} {relation : SweepGapRelation}

/-- A directional cup witness survives enlargement inside the same ambient order. -/
theorem ContainsCupSetAtGap.mono (h : ContainsCupSetAtGap χ t r g relation)
    (hts : t ⊆ s) : ContainsCupSetAtGap χ s r g relation := by
  obtain ⟨cup, hcup, hcard, hmono, hrelation⟩ := h
  exact ⟨cup, hcup.trans hts, hcard, hmono, hrelation⟩

/-- A directional cap witness survives enlargement inside the same ambient order. -/
theorem ContainsCapSetAtGap.mono (h : ContainsCapSetAtGap χ t r g relation)
    (hts : t ⊆ s) : ContainsCapSetAtGap χ s r g relation := by
  obtain ⟨cap, hcap, hcard, hmono, hrelation⟩ := h
  exact ⟨cap, hcap.trans hts, hcard, hmono, hrelation⟩

end FinsetPolygon

end


end ErdosSzekeres
