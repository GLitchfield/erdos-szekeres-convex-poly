module

public import ErdosSzekeres.RankProfile

@[expose] public section

namespace ErdosSzekeres
namespace TurnLanguage

variable {α : Type*}

/-- Consecutive turns of a vertex list, in chronological order. -/
def turnSequence (κ : α → α → α → Turn) : List α → List Turn
  | a :: b :: c :: tail => κ a b c :: turnSequence κ (b :: c :: tail)
  | _ => []

@[simp] theorem turnSequence_length (κ : α → α → α → Turn) (l : List α) :
    (turnSequence κ l).length = l.length - 2 := by
  induction l with
  | nil => simp [turnSequence]
  | cons a l ih =>
      cases l with
      | nil => simp [turnSequence]
      | cons b l =>
          cases l with
          | nil => simp [turnSequence]
          | cons c l => simpa [turnSequence] using ih

@[simp] theorem turnSequence_append_triple (κ : α → α → α → Turn)
    (pre : List α) (w u v : α) :
    turnSequence κ (pre ++ [w, u, v]) =
      turnSequence κ (pre ++ [w, u]) ++ [κ w u v] := by
  cases pre with
  | nil => simp [turnSequence]
  | cons a tail =>
      cases tail with
      | nil => simp [turnSequence]
      | cons b tail =>
          cases tail with
          | nil => simp [turnSequence]
          | cons c tail =>
              simp only [List.cons_append, turnSequence, List.cons.injEq]
              exact ⟨trivial, turnSequence_append_triple κ (b :: c :: tail) w u v⟩
termination_by pre.length

variable [LinearOrder α]

/-- A chronological turn word realized by an increasing chain ending at
`(u,v)` whose vertices all lie in `s`. -/
def HasPairTurnWord (κ : α → α → α → Turn) (s : Finset α)
    (u v : α) (word : List Turn) : Prop :=
  ∃ pre : List α,
    (pre ++ [u, v]).IsChain (· < ·) ∧
      CupCap.ListIn (pre ++ [u, v]) s ∧
      turnSequence κ (pre ++ [u, v]) = word

theorem hasPairTurnWord_nil_iff (κ : α → α → α → Turn)
    (s : Finset α) (u v : α) :
    HasPairTurnWord κ s u v [] ↔ u < v ∧ u ∈ s ∧ v ∈ s := by
  constructor
  · rintro ⟨pre, hchain, hin, hword⟩
    have hlength := congrArg List.length hword
    simp only [turnSequence_length, List.length_append, List.length_cons,
      List.length_nil] at hlength
    have hpre : pre = [] := List.length_eq_zero_iff.mp (by omega)
    subst pre
    simpa [CupCap.ListIn] using And.intro hchain hin
  · rintro ⟨huv, hu, hv⟩
    exact ⟨[], by simpa, by simp [CupCap.ListIn, hu, hv], by simp [turnSequence]⟩

theorem hasPairTurnWord_append_iff (κ : α → α → α → Turn)
    (s : Finset α) (u v : α) (word : List Turn) (c : Turn) :
    HasPairTurnWord κ s u v (word ++ [c]) ↔
      u < v ∧ v ∈ s ∧ ∃ w : α, w ∈ s ∧ w < u ∧
        HasPairTurnWord κ s w u word ∧ κ w u v = c := by
  constructor
  · rintro ⟨pre, hchain, hin, hword⟩
    have hpre : pre ≠ [] := by
      intro heq
      subst pre
      simp [turnSequence] at hword
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
        have hchain' :
            (revpre.reverse ++ [w, u, v]).IsChain (· < ·) := by
          simpa [hpreEq, List.append_assoc] using hchain
        have hparts := List.isChain_append_cons_cons.mp
          (show (revpre.reverse ++ [w] ++ u :: v :: []).IsChain (· < ·) by
            simpa [List.append_assoc] using hchain')
        have hprevious :
            (revpre.reverse ++ [w, u]).IsChain (· < ·) := by
          simpa [List.append_assoc] using hparts.1
        have hwu : w < u := by
          have hsuffix := hprevious.right_of_append
            (l₁ := revpre.reverse) (l₂ := [w, u])
          simpa using hsuffix
        have huv : u < v := hparts.2.1
        have hw : w ∈ s := hin w (by simp [hpreEq])
        have hv : v ∈ s := hin v (by simp)
        have hpreviousIn : CupCap.ListIn (revpre.reverse ++ [w, u]) s := by
          intro x hx
          exact hin x (by simp [hpreEq] at hx ⊢; aesop)
        have hturns :
            turnSequence κ (revpre.reverse ++ [w, u, v]) = word ++ [c] := by
          simpa [hpreEq, List.append_assoc] using hword
        rw [turnSequence_append_triple] at hturns
        have heq : turnSequence κ (revpre.reverse ++ [w, u]) = word ∧
            κ w u v = c := by
          have hlength :
              (turnSequence κ (revpre.reverse ++ [w, u])).length =
                word.length := by
            have h := congrArg List.length hturns
            simp only [List.length_append, List.length_singleton] at h
            exact Nat.add_right_cancel h
          have h := List.append_inj hturns hlength
          exact ⟨h.1, by simpa using h.2⟩
        exact ⟨huv, hv, w, hw, hwu,
          ⟨revpre.reverse, hprevious, hpreviousIn, heq.1⟩, heq.2⟩
  · rintro ⟨huv, hv, w, hw, hwu, hword, hturn⟩
    rcases hword with ⟨pre, hchain, hin, hword⟩
    refine ⟨pre ++ [w], ?_, ?_, ?_⟩
    · show ((pre ++ [w]) ++ u :: v :: []).IsChain (· < ·)
      exact List.isChain_append_cons_cons.mpr
        ⟨by simpa [List.append_assoc] using hchain, huv, by simp⟩
    · intro x hx
      simp at hx
      rcases hx with hx | hxw | hxu | hxv
      · exact hin x (by simp [hx])
      · simpa [hxw] using hw
      · simpa [hxu] using hin u (by simp)
      · simpa [hxv] using hv
    · have h : turnSequence κ (pre ++ [w, u, v]) = word ++ [c] := by
        rw [turnSequence_append_triple, hword, hturn]
      simpa [List.append_assoc] using h

/-- If every predecessor triple ending at `(u,v)` has the same turn `c`, the
new words ending at `(u,v)` are exactly `c` appended to words from an incoming
pair at `u`. -/
theorem hasPairTurnWord_append_of_constant (κ : α → α → α → Turn)
    (s : Finset α) (u v : α) (word : List Turn) (c : Turn)
    (hconstant : ∀ w ∈ s, w < u → κ w u v = c) :
    HasPairTurnWord κ s u v (word ++ [c]) ↔
      u < v ∧ v ∈ s ∧ ∃ w : α, w ∈ s ∧ w < u ∧
        HasPairTurnWord κ s w u word := by
  rw [hasPairTurnWord_append_iff]
  constructor
  · rintro ⟨huv, hv, w, hw, hwu, hword, _⟩
    exact ⟨huv, hv, w, hw, hwu, hword⟩
  · rintro ⟨huv, hv, w, hw, hwu, hword⟩
    exact ⟨huv, hv, w, hw, hwu, hword, hconstant w hw hwu⟩

/-- Kernel-reducible predecessor recurrence.  The argument is the turn word in
reverse chronological order, so the newest turn is its head. -/
def reversePairTurnWordBool {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (u v : Fin n) : List Turn → Bool
  | [] => decide (u < v ∧ u ∈ s ∧ v ∈ s)
  | c :: reverseWord =>
      decide (u < v ∧ v ∈ s) && (List.finRange n).any fun w ↦
        decide (w ∈ s ∧ w < u) &&
          reversePairTurnWordBool κ s w u reverseWord &&
          decide (RankProfile.turnOfColoring κ w u v = c)

/-- Executable membership test for chronological pair turn words. -/
def pairTurnWordBool {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (u v : Fin n) (word : List Turn) : Bool :=
  reversePairTurnWordBool κ s u v word.reverse

theorem reversePairTurnWordBool_eq_true_iff {n : ℕ}
    (κ : TripleColoring n) (s : Finset (Fin n)) (u v : Fin n)
    (reverseWord : List Turn) :
    reversePairTurnWordBool κ s u v reverseWord = true ↔
      HasPairTurnWord (RankProfile.turnOfColoring κ) s u v
        reverseWord.reverse := by
  induction reverseWord generalizing u v with
  | nil => simpa [reversePairTurnWordBool] using
      (hasPairTurnWord_nil_iff (RankProfile.turnOfColoring κ) s u v).symm
  | cons c reverseWord ih =>
      rw [List.reverse_cons]
      simpa [reversePairTurnWordBool, ih, List.mem_finRange, and_assoc] using
        (hasPairTurnWord_append_iff
          (RankProfile.turnOfColoring κ) s u v reverseWord.reverse c).symm

theorem pairTurnWordBool_eq_true_iff {n : ℕ}
    (κ : TripleColoring n) (s : Finset (Fin n)) (u v : Fin n)
    (word : List Turn) :
    pairTurnWordBool κ s u v word = true ↔
      HasPairTurnWord (RankProfile.turnOfColoring κ) s u v word := by
  simpa [pairTurnWordBool] using
    reversePairTurnWordBool_eq_true_iff κ s u v word.reverse

/-- All binary turn words of exactly the given length. -/
def turnWordsExact : ℕ → Finset (List Turn)
  | 0 => {[]}
  | d + 1 =>
      (turnWordsExact d).image (Turn.left :: ·) ∪
        (turnWordsExact d).image (Turn.right :: ·)

/-- All binary turn words of length at most `d`. -/
def turnWordsUpTo (d : ℕ) : Finset (List Turn) :=
  (Finset.range (d + 1)).biUnion turnWordsExact

theorem mem_turnWordsExact_iff (word : List Turn) (d : ℕ) :
    word ∈ turnWordsExact d ↔ word.length = d := by
  induction d generalizing word with
  | zero => simp [turnWordsExact]
  | succ d ih =>
      cases word with
      | nil => simp [turnWordsExact]
      | cons c word =>
          cases c <;> simp [turnWordsExact, ih]

theorem mem_turnWordsUpTo_iff (word : List Turn) (d : ℕ) :
    word ∈ turnWordsUpTo d ↔ word.length ≤ d := by
  simp [turnWordsUpTo, mem_turnWordsExact_iff]

/-- The depth-bounded chronological language at an ordered endpoint pair. -/
def pairTurnLanguage {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (d : ℕ) (u v : Fin n) : Finset (List Turn) :=
  (turnWordsUpTo d).filter fun word ↦ pairTurnWordBool κ s u v word

theorem mem_pairTurnLanguage_iff {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (d : ℕ) (u v : Fin n) (word : List Turn) :
    word ∈ pairTurnLanguage κ s d u v ↔
      word.length ≤ d ∧
        HasPairTurnWord (RankProfile.turnOfColoring κ) s u v word := by
  simp [pairTurnLanguage, mem_turnWordsUpTo_iff,
    pairTurnWordBool_eq_true_iff]

/-- Endpoint-forgetting support of all pair languages on `s`. -/
def pairTurnSpectrum {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (d : ℕ) : Finset (Finset (List Turn)) :=
  ((s ×ˢ s).filter fun pair ↦ pair.1 < pair.2).image fun pair ↦
    pairTurnLanguage κ s d pair.1 pair.2

/-- The endpoint-sensitive incoming star at `v`, with predecessor identities
forgotten but their complete language values retained. -/
def incomingStar {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (d : ℕ) (v : Fin n) :
    Finset (Finset (List Turn)) :=
  (s.filter (· < v)).image fun u ↦ pairTurnLanguage κ s d u v

/-- Endpoint identities forgotten only after grouping incoming pair languages
by their common terminal vertex. -/
def incomingStarSpectrum {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (d : ℕ) : Finset (Finset (Finset (List Turn))) :=
  s.image fun v ↦ incomingStar κ s d v

end TurnLanguage
end ErdosSzekeres

end
