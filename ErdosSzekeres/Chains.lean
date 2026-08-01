import ErdosSzekeres.Sweep

/-!
# Consecutive and all-triples cup/cap chains

The recurrence-friendly definition of a cup or cap checks only consecutive
triples in the selected sequence.  This file proves that, for colorings induced
by actual swept configurations, that local definition is equivalent to the
all-triples definition in `Sweep.lean`.

The geometric input is a four-point propagation identity.  For four points in
strict sweep order, equal positive signs on the two consecutive triples force
positive signs on both spanning triples; the negative statement is symmetric.
Strong induction on the outer index span then propagates the consecutive signs
to every triple.
-/

namespace ErdosSzekeres

noncomputable section

/-- A selected increasing sequence whose consecutive triples all have color
`c`. -/
def IsConsecutiveMonochromaticChain {n k : ℕ} (χ : TripleColoring n) (c : Turn)
    (f : Fin k → Fin n) : Prop :=
  ∃ hf : StrictMono f,
    ∀ (i j l : Fin k), (hij : i < j) → (hjl : j < l) →
      j.val = i.val + 1 → l.val = j.val + 1 →
        χ ⟨f i, f j, f l, hf hij, hf hjl⟩ = c

/-- The consecutive-triples version of a cup. -/
abbrev IsConsecutiveCup {n k : ℕ} (χ : TripleColoring n)
    (f : Fin k → Fin n) : Prop :=
  IsConsecutiveMonochromaticChain χ Turn.left f

/-- The consecutive-triples version of a cap. -/
abbrev IsConsecutiveCap {n k : ℕ} (χ : TripleColoring n)
    (f : Fin k → Fin n) : Prop :=
  IsConsecutiveMonochromaticChain χ Turn.right f

namespace SweptConfiguration

variable {n : ℕ} (P : SweptConfiguration n)

/-- The consecutive-turn predicate on all indices of a swept configuration. -/
private def HasConsecutiveTurns (c : Turn) : Prop :=
  ∀ (i j k : Fin n), (hij : i < j) → (hjk : j < k) →
    j.val = i.val + 1 → k.val = j.val + 1 → P.turn i j k = c

private theorem orientation_propagate_pos (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (habc : 0 < orientation a b c) (hbcd : 0 < orientation b c d) :
    0 < orientation a b d ∧ 0 < orientation a c d := by
  simp only [orientation] at *
  constructor <;> nlinarith

private theorem orientation_propagate_neg (a b c d : Point 2)
    (hab : a 0 < b 0) (hbc : b 0 < c 0) (hcd : c 0 < d 0)
    (habc : orientation a b c < 0) (hbcd : orientation b c d < 0) :
    orientation a b d < 0 ∧ orientation a c d < 0 := by
  simp only [orientation] at *
  constructor <;> nlinarith

private theorem all_left_of_consecutive
    (hlocal : P.HasConsecutiveTurns Turn.left) :
    ∀ (i j k : Fin n), (hij : i < j) → (hjk : j < k) →
      P.turn i j k = Turn.left := by
  have aux : ∀ span : ℕ, ∀ (i j k : Fin n), k.val - i.val = span →
      (hij : i < j) → (hjk : j < k) →
      0 < orientation (P.point i) (P.point j) (P.point k) := by
    intro span
    induction span using Nat.strong_induction_on with
    | h span ih =>
      intro i j k hspan hij hjk
      by_cases hij_succ : j.val = i.val + 1
      · by_cases hjk_succ : k.val = j.val + 1
        · exact (P.turn_eq_left_iff i j k).mp
            (hlocal i j k hij hjk hij_succ hjk_succ)
        · let m : Fin n := ⟨k.val - 1, by omega⟩
          have hjm : j < m := by
            change j.val < k.val - 1
            omega
          have hmk : m < k := by
            change k.val - 1 < k.val
            omega
          have hfirst : 0 < orientation (P.point i) (P.point j) (P.point m) :=
            ih (m.val - i.val) (by dsimp [m]; omega) i j m rfl hij hjm
          have hsecond : 0 < orientation (P.point j) (P.point m) (P.point k) :=
            ih (k.val - j.val) (by omega) j m k rfl hjm hmk
          exact (orientation_propagate_pos
            (P.point i) (P.point j) (P.point m) (P.point k)
            (P.sweep_strictMono hij) (P.sweep_strictMono hjm)
            (P.sweep_strictMono hmk) hfirst hsecond).1
      · let m : Fin n := ⟨j.val - 1, by omega⟩
        have him : i < m := by
          change i.val < j.val - 1
          omega
        have hmj : m < j := by
          change j.val - 1 < j.val
          omega
        have hfirst : 0 < orientation (P.point i) (P.point m) (P.point j) :=
          ih (j.val - i.val) (by omega) i m j rfl him hmj
        have hsecond : 0 < orientation (P.point m) (P.point j) (P.point k) :=
          ih (k.val - m.val) (by dsimp [m]; omega) m j k rfl hmj hjk
        exact (orientation_propagate_pos
          (P.point i) (P.point m) (P.point j) (P.point k)
          (P.sweep_strictMono him) (P.sweep_strictMono hmj)
          (P.sweep_strictMono hjk) hfirst hsecond).2
  intro i j k hij hjk
  rw [P.turn_eq_left_iff]
  exact aux (k.val - i.val) i j k rfl hij hjk

private theorem all_right_of_consecutive
    (hlocal : P.HasConsecutiveTurns Turn.right) :
    ∀ (i j k : Fin n), (hij : i < j) → (hjk : j < k) →
      P.turn i j k = Turn.right := by
  have aux : ∀ span : ℕ, ∀ (i j k : Fin n), k.val - i.val = span →
      (hij : i < j) → (hjk : j < k) →
      orientation (P.point i) (P.point j) (P.point k) < 0 := by
    intro span
    induction span using Nat.strong_induction_on with
    | h span ih =>
      intro i j k hspan hij hjk
      by_cases hij_succ : j.val = i.val + 1
      · by_cases hjk_succ : k.val = j.val + 1
        · exact (P.turn_eq_right_iff i j k hij hjk).mp
            (hlocal i j k hij hjk hij_succ hjk_succ)
        · let m : Fin n := ⟨k.val - 1, by omega⟩
          have hjm : j < m := by
            change j.val < k.val - 1
            omega
          have hmk : m < k := by
            change k.val - 1 < k.val
            omega
          have hfirst : orientation (P.point i) (P.point j) (P.point m) < 0 :=
            ih (m.val - i.val) (by dsimp [m]; omega) i j m rfl hij hjm
          have hsecond : orientation (P.point j) (P.point m) (P.point k) < 0 :=
            ih (k.val - j.val) (by omega) j m k rfl hjm hmk
          exact (orientation_propagate_neg
            (P.point i) (P.point j) (P.point m) (P.point k)
            (P.sweep_strictMono hij) (P.sweep_strictMono hjm)
            (P.sweep_strictMono hmk) hfirst hsecond).1
      · let m : Fin n := ⟨j.val - 1, by omega⟩
        have him : i < m := by
          change i.val < j.val - 1
          omega
        have hmj : m < j := by
          change j.val - 1 < j.val
          omega
        have hfirst : orientation (P.point i) (P.point m) (P.point j) < 0 :=
          ih (j.val - i.val) (by omega) i m j rfl him hmj
        have hsecond : orientation (P.point m) (P.point j) (P.point k) < 0 :=
          ih (k.val - m.val) (by dsimp [m]; omega) m j k rfl hmj hjk
        exact (orientation_propagate_neg
          (P.point i) (P.point m) (P.point j) (P.point k)
          (P.sweep_strictMono him) (P.sweep_strictMono hmj)
          (P.sweep_strictMono hjk) hfirst hsecond).2
  intro i j k hij hjk
  rw [P.turn_eq_right_iff i j k hij hjk]
  exact aux (k.val - i.val) i j k rfl hij hjk

private theorem all_turns_of_consecutive (c : Turn)
    (hlocal : P.HasConsecutiveTurns c) :
    ∀ (i j k : Fin n), (hij : i < j) → (hjk : j < k) →
      P.turn i j k = c := by
  cases c with
  | left => exact P.all_left_of_consecutive hlocal
  | right => exact P.all_right_of_consecutive hlocal

/-- On a sweep-realizable coloring, checking every triple of a selected chain
is equivalent to checking just its consecutive triples. -/
theorem isMonochromaticChain_iff_isConsecutiveMonochromaticChain
    {k : ℕ} (c : Turn) (f : Fin k → Fin n) :
    IsMonochromaticChain P.tripleColoring c f ↔
      IsConsecutiveMonochromaticChain P.tripleColoring c f := by
  constructor
  · rintro ⟨hf, hall⟩
    refine ⟨hf, ?_⟩
    intro i j l hij hjl _ _
    exact hall hij hjl
  · rintro ⟨hf, hlocal⟩
    let e : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono f hf
    let Q : SweptConfiguration k := P.restrict e
    have hQlocal : Q.HasConsecutiveTurns c := by
      intro i j l hij hjl hij_succ hjl_succ
      change P.turn (f i) (f j) (f l) = c
      exact hlocal i j l hij hjl hij_succ hjl_succ
    refine ⟨hf, ?_⟩
    intro i j l hij hjl
    have hturn := Q.all_turns_of_consecutive c hQlocal i j l hij hjl
    exact hturn

/-- A selected sequence is a cup iff all its consecutive triples turn left. -/
theorem isCup_iff_isConsecutiveCup {k : ℕ} (f : Fin k → Fin n) :
    IsCup P.tripleColoring f ↔ IsConsecutiveCup P.tripleColoring f :=
  P.isMonochromaticChain_iff_isConsecutiveMonochromaticChain Turn.left f

/-- A selected sequence is a cap iff all its consecutive triples turn right. -/
theorem isCap_iff_isConsecutiveCap {k : ℕ} (f : Fin k → Fin n) :
    IsCap P.tripleColoring f ↔ IsConsecutiveCap P.tripleColoring f :=
  P.isMonochromaticChain_iff_isConsecutiveMonochromaticChain Turn.right f

end SweptConfiguration

/-- Realizability-witness form of the consecutive/all-triples chain
equivalence. -/
theorem IsSweepRealizable.isMonochromaticChain_iff_isConsecutive
    {n k : ℕ} {χ : TripleColoring n} (hχ : IsSweepRealizable χ)
    (c : Turn) (f : Fin k → Fin n) :
    IsMonochromaticChain χ c f ↔ IsConsecutiveMonochromaticChain χ c f := by
  obtain ⟨P, rfl⟩ := hχ
  exact P.isMonochromaticChain_iff_isConsecutiveMonochromaticChain c f

/-- Realizability-witness form of the consecutive cup equivalence. -/
theorem IsSweepRealizable.isCup_iff_isConsecutiveCup
    {n k : ℕ} {χ : TripleColoring n} (hχ : IsSweepRealizable χ)
    (f : Fin k → Fin n) :
    IsCup χ f ↔ IsConsecutiveCup χ f :=
  hχ.isMonochromaticChain_iff_isConsecutive Turn.left f

/-- Realizability-witness form of the consecutive cap equivalence. -/
theorem IsSweepRealizable.isCap_iff_isConsecutiveCap
    {n k : ℕ} {χ : TripleColoring n} (hχ : IsSweepRealizable χ)
    (f : Fin k → Fin n) :
    IsCap χ f ↔ IsConsecutiveCap χ f :=
  hχ.isMonochromaticChain_iff_isConsecutive Turn.right f

end

end ErdosSzekeres
