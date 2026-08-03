module

public import ErdosSzekeres.CupCap

@[expose] public section

/-!
# Consecutive pair ranks and vertex downsets

This file gives a specification-first Lean interface for the rank/downset
states used in the E3 singleton-root falsification gate. It deliberately uses
`CupCap.IsTurnChain` directly: no signotope, recursive decomposition, or
sweep-realizability assumption is needed to state the rank semantics.

The rank of an ordered pair is one less than the length of a same-turn
consecutive chain ending at that pair. `HasClippedPairRankAtLeast` records a
threshold within a fixed clip. A point `(cap,cup)` lies in the predecessor
downset of `v` when one incoming pair `(u,v)` reaches both thresholds.
-/

namespace ErdosSzekeres
namespace RankProfile

variable {α : Type*} [LinearOrder α]

/-- Interpret an ambient triple coloring as a ternary turn function. Values on
non-increasing inputs are irrelevant to increasing turn chains. -/
def turnOfColoring {n : ℕ} (κ : TripleColoring n) (a b c : Fin n) : Turn :=
  if hab : a < b then
    if hbc : b < c then κ ⟨a, b, c, hab, hbc⟩ else Turn.right
  else Turn.right

/-- Kernel-reducible dynamic program for consecutive pair-rank thresholds.
At level zero, `(u,v)` is an increasing pair in `s`. Each successor level
prepends one vertex making the requested turn. -/
def finitePairRankAboveBool {n : ℕ} (κ : TripleColoring n) (c : Turn)
    (s : Finset (Fin n)) (u v : Fin n) : ℕ → Bool
  | 0 => decide (u < v ∧ u ∈ s ∧ v ∈ s)
  | q + 1 =>
      decide (u < v ∧ v ∈ s) && (List.finRange n).any fun w ↦
        decide (w ∈ s ∧ w < u) && finitePairRankAboveBool κ c s w u q &&
          decide (turnOfColoring κ w u v = c)

/-- Propositional recurrence computed by `finitePairRankAboveBool`. -/
def HasRecursivePairRankAbove {n : ℕ} (κ : TripleColoring n) (c : Turn)
    (s : Finset (Fin n)) (u v : Fin n) : ℕ → Prop
  | 0 => u < v ∧ u ∈ s ∧ v ∈ s
  | q + 1 => u < v ∧ v ∈ s ∧ ∃ w : Fin n,
      w ∈ s ∧ w < u ∧ HasRecursivePairRankAbove κ c s w u q ∧
        turnOfColoring κ w u v = c

theorem finitePairRankAboveBool_eq_true_iff {n : ℕ}
    (κ : TripleColoring n) (c : Turn) (s : Finset (Fin n))
    (u v : Fin n) (q : ℕ) :
    finitePairRankAboveBool κ c s u v q = true ↔
      HasRecursivePairRankAbove κ c s u v q := by
  induction q generalizing u v with
  | zero => simp [finitePairRankAboveBool, HasRecursivePairRankAbove]
  | succ q ih =>
      simp [finitePairRankAboveBool, HasRecursivePairRankAbove,
        List.any_eq_true, ih]
      aesop

/-- The pair `(u,v)` has consecutive rank at least `q+1` in the finite set
`s`, represented by the kernel-reducible dynamic program above. -/
abbrev HasFinitePairRankAbove {n : ℕ} (κ : TripleColoring n) (c : Turn)
    (s : Finset (Fin n)) (u v : Fin n) (q : ℕ) : Prop :=
  finitePairRankAboveBool κ c s u v q = true

def HasPairRankAtLeast (κ : α → α → α → Turn) (c : Turn)
    (s : Finset α) (u v : α) (r : ℕ) : Prop :=
  ∃ pre : List α,
    CupCap.IsTurnChain κ c (pre ++ [u, v]) ∧
      CupCap.ListIn (pre ++ [u, v]) s ∧
      r + 1 ≤ (pre ++ [u, v]).length

theorem hasPairRankAtLeast_one (κ : α → α → α → Turn) (c : Turn)
    {s : Finset α} {u v : α} (hu : u ∈ s) (hv : v ∈ s) (huv : u < v) :
    HasPairRankAtLeast κ c s u v 1 := by
  refine ⟨[], ?_, ?_, by simp⟩
  · simp [huv]
  · simp [CupCap.ListIn, hu, hv]

theorem hasRecursivePairRankAbove_iff_hasPairRankAtLeast {n : ℕ}
    (κ : TripleColoring n) (c : Turn) (s : Finset (Fin n))
    (u v : Fin n) (q : ℕ) :
    HasRecursivePairRankAbove κ c s u v q ↔
      HasPairRankAtLeast (turnOfColoring κ) c s u v (q + 1) := by
  induction q generalizing u v with
  | zero =>
      constructor
      · rintro ⟨huv, hu, hv⟩
        exact hasPairRankAtLeast_one (turnOfColoring κ) c hu hv huv
      · rintro ⟨pre, hchain, hin, _⟩
        have hsuffix := hchain.1.right_of_append (l₁ := pre) (l₂ := [u, v])
        have huv : u < v := by simpa using hsuffix
        exact ⟨huv, hin u (by simp), hin v (by simp)⟩
  | succ q ih =>
      constructor
      · rintro ⟨huv, hv, w, hw, hwu, hrank, hturn⟩
        obtain ⟨pre, hchain, hin, hlength⟩ := (ih w u).mp hrank
        refine ⟨pre ++ [w], ?_, ?_, ?_⟩
        · rw [List.append_assoc]
          simpa using (CupCap.isTurnChain_append_cons3.mpr
            ⟨hchain, hturn, CupCap.isTurnChain_pair.mpr huv⟩)
        · intro x hx
          simp at hx
          rcases hx with hx | hxw | hxu | hxv
          · exact hin x (by simp [hx])
          · simpa [hxw] using hw
          · simpa [hxu] using hin u (by simp)
          · simpa [hxv] using hv
        · simp at hlength ⊢
          omega
      · rintro ⟨pre, hchain, hin, hlength⟩
        have hpre : pre ≠ [] := by
          intro heq
          subst pre
          simp at hlength
        cases hrev : pre.reverse with
        | nil =>
            have : pre = [] := by
              have := congrArg List.reverse hrev
              simpa using this
            exact (hpre this).elim
        | cons w revpre =>
            have hpreEq : pre = revpre.reverse ++ [w] := by
              have h := congrArg List.reverse hrev
              simpa using h
            have hchain' : CupCap.IsTurnChain (turnOfColoring κ) c
                (revpre.reverse ++ w :: u :: v :: []) := by
              simpa [hpreEq, List.append_assoc] using hchain
            obtain ⟨hprevious, hturn, huvChain⟩ :=
              CupCap.isTurnChain_append_cons3.mp hchain'
            have hwu : w < u := by
              have hsuffix := hprevious.1.right_of_append
                (l₁ := revpre.reverse) (l₂ := [w, u])
              simpa using hsuffix
            have huv : u < v := CupCap.isTurnChain_pair.mp huvChain
            have hw : w ∈ s := hin w (by simp [hpreEq])
            have hv : v ∈ s := hin v (by simp)
            have hpreviousLength : q + 2 ≤ (revpre.reverse ++ [w, u]).length := by
              simp [hpreEq] at hlength ⊢
              omega
            have hpreviousIn : CupCap.ListIn (revpre.reverse ++ [w, u]) s := by
              intro x hx
              exact hin x (by simp [hpreEq] at hx ⊢; aesop)
            have hrank : HasRecursivePairRankAbove κ c s w u q :=
              (ih w u).mpr ⟨revpre.reverse, hprevious, hpreviousIn,
                hpreviousLength⟩
            exact ⟨huv, hv, w, hw, hwu, hrank, hturn⟩

theorem hasFinitePairRankAbove_iff_hasPairRankAtLeast {n : ℕ}
    (κ : TripleColoring n) (c : Turn) (s : Finset (Fin n))
    (u v : Fin n) (q : ℕ) :
    HasFinitePairRankAbove κ c s u v q ↔
      HasPairRankAtLeast (turnOfColoring κ) c s u v (q + 1) :=
  (finitePairRankAboveBool_eq_true_iff κ c s u v q).trans
    (hasRecursivePairRankAbove_iff_hasPairRankAtLeast κ c s u v q)

/-- Equality of the complete two-color clipped pair-rank states on `s`.
For every ordered endpoint pair, it compares all rank thresholds from one
through `clip`. -/
def FinitePairRankStateEq {n : ℕ} (κ ψ : TripleColoring n)
    (s : Finset (Fin n)) (clip : ℕ) : Prop :=
  ∀ u v (q : Fin clip),
    (HasFinitePairRankAbove κ Turn.left s u v q.val ↔
      HasFinitePairRankAbove ψ Turn.left s u v q.val) ∧
    (HasFinitePairRankAbove κ Turn.right s u v q.val ↔
      HasFinitePairRankAbove ψ Turn.right s u v q.val)

def HasClippedPairRankAtLeast (κ : α → α → α → Turn) (c : Turn)
    (s : Finset α) (clip : ℕ) (u v : α) (r : ℕ) : Prop :=
  r ≤ clip ∧ HasPairRankAtLeast κ c s u v r

def InVertexDownset (κ : α → α → α → Turn) (s : Finset α)
    (clip : ℕ) (v : α) (cap cup : ℕ) : Prop :=
  1 ≤ cap ∧ 1 ≤ cup ∧
    ∃ u ∈ s, u < v ∧
      HasClippedPairRankAtLeast κ Turn.right s clip u v cap ∧
      HasClippedPairRankAtLeast κ Turn.left s clip u v cup

theorem HasPairRankAtLeast.mono {κ : α → α → α → Turn} {c : Turn}
    {t s : Finset α} {u v : α} {r : ℕ} (hts : t ⊆ s) :
    HasPairRankAtLeast κ c t u v r → HasPairRankAtLeast κ c s u v r := by
  rintro ⟨pre, hchain, hin, hlength⟩
  exact ⟨pre, hchain, fun x hx => hts (hin x hx), hlength⟩

theorem HasPairRankAtLeast.anti {κ : α → α → α → Turn} {c : Turn}
    {s : Finset α} {u v : α} {r' r : ℕ} (hrr : r' ≤ r) :
    HasPairRankAtLeast κ c s u v r → HasPairRankAtLeast κ c s u v r' := by
  rintro ⟨pre, hchain, hin, hlength⟩
  refine ⟨pre, hchain, hin, ?_⟩
  omega

theorem HasClippedPairRankAtLeast.mono {κ : α → α → α → Turn} {c : Turn}
    {t s : Finset α} {clip : ℕ} {u v : α} {r : ℕ} (hts : t ⊆ s) :
    HasClippedPairRankAtLeast κ c t clip u v r →
      HasClippedPairRankAtLeast κ c s clip u v r := by
  rintro ⟨hclip, hrank⟩
  exact ⟨hclip, hrank.mono hts⟩

theorem HasClippedPairRankAtLeast.anti {κ : α → α → α → Turn} {c : Turn}
    {s : Finset α} {clip : ℕ} {u v : α} {r' r : ℕ} (hrr : r' ≤ r) :
    HasClippedPairRankAtLeast κ c s clip u v r →
      HasClippedPairRankAtLeast κ c s clip u v r' := by
  rintro ⟨hclip, hrank⟩
  exact ⟨hrr.trans hclip, hrank.anti hrr⟩

theorem InVertexDownset.mono {κ : α → α → α → Turn}
    {t s : Finset α} {clip : ℕ} {v : α} {cap cup : ℕ} (hts : t ⊆ s) :
    InVertexDownset κ t clip v cap cup →
      InVertexDownset κ s clip v cap cup := by
  rintro ⟨hcap, hcup, u, hu, huv, hcapRank, hcupRank⟩
  exact ⟨hcap, hcup, u, hts hu, huv, hcapRank.mono hts, hcupRank.mono hts⟩

theorem InVertexDownset.lower_closed {κ : α → α → α → Turn}
    {s : Finset α} {clip : ℕ} {v : α} {cap' cap cup' cup : ℕ}
    (hcap' : 1 ≤ cap') (hcup' : 1 ≤ cup') (hcap : cap' ≤ cap)
    (hcup : cup' ≤ cup) :
    InVertexDownset κ s clip v cap cup →
      InVertexDownset κ s clip v cap' cup' := by
  rintro ⟨_, _, u, hu, huv, hcapRank, hcupRank⟩
  exact ⟨hcap', hcup', u, hu, huv, hcapRank.anti hcap, hcupRank.anti hcup⟩

theorem InVertexDownset.cap_le_clip {κ : α → α → α → Turn}
    {s : Finset α} {clip : ℕ} {v : α} {cap cup : ℕ}
    (h : InVertexDownset κ s clip v cap cup) : cap ≤ clip := by
  obtain ⟨_, _, _, _, _, hcap, _⟩ := h
  exact hcap.1

theorem InVertexDownset.cup_le_clip {κ : α → α → α → Turn}
    {s : Finset α} {clip : ℕ} {v : α} {cap cup : ℕ}
    (h : InVertexDownset κ s clip v cap cup) : cup ≤ clip := by
  obtain ⟨_, _, _, _, _, _, hcup⟩ := h
  exact hcup.1

end RankProfile
end ErdosSzekeres
