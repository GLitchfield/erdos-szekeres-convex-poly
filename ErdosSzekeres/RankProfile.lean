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

def HasPairRankAtLeast (κ : α → α → α → Turn) (c : Turn)
    (s : Finset α) (u v : α) (r : ℕ) : Prop :=
  ∃ pre : List α,
    CupCap.IsTurnChain κ c (pre ++ [u, v]) ∧
      CupCap.ListIn (pre ++ [u, v]) s ∧
      r + 1 ≤ (pre ++ [u, v]).length

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

theorem hasPairRankAtLeast_one (κ : α → α → α → Turn) (c : Turn)
    {s : Finset α} {u v : α} (hu : u ∈ s) (hv : v ∈ s) (huv : u < v) :
    HasPairRankAtLeast κ c s u v 1 := by
  refine ⟨[], ?_, ?_, by simp⟩
  · simp [huv]
  · simp [CupCap.ListIn, hu, hv]

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
