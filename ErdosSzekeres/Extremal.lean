import ErdosSzekeres.Composition

/-!
# Recursive cup--cap extremal configurations

This file packages the deep-composition machinery into the sharpness
construction for the cup--cap theorem. Parameters `p` and `q` measure the
largest permitted cap and cup beyond the unavoidable single vertex.
-/

namespace ErdosSzekeres

noncomputable section

/-- A one-point swept configuration, used on the boundary of Pascal's
triangle. -/
def singletonConfiguration : SweptConfiguration 1 where
  point := fun _ => ![0, 0]
  sweep_strictMono := by
    intro i j hij
    omega
  generalPosition := by
    intro i j k hij
    exact (hij (Subsingleton.elim i j)).elim

theorem singleton_chainSizeAtMost (c : Turn) :
    ChainSizeAtMost singletonConfiguration.tripleColoring c 1 := by
  intro k f hchain
  have hf : Function.Injective f := hchain.choose.injective
  simpa using Fintype.card_le_of_injective f hf

/-- The invariant required at the `(p,q)` entry of Pascal's triangle: caps
have size at most `p+1`, and cups have size at most `q+1`. -/
def HasCupCapBounds {N : ℕ} (P : SweptConfiguration N) (p q : ℕ) : Prop :=
  ChainSizeAtMost P.tripleColoring Turn.right (p + 1) ∧
  ChainSizeAtMost P.tripleColoring Turn.left (q + 1)

theorem singleton_hasCupCapBounds (p q : ℕ) :
    HasCupCapBounds singletonConfiguration p q := by
  constructor
  · intro k f hchain
    exact (singleton_chainSizeAtMost Turn.right hchain).trans (by omega)
  · intro k f hchain
    exact (singleton_chainSizeAtMost Turn.left hchain).trans (by omega)

/-- The Pascal step is realized geometrically by a deep composition. -/
theorem exists_cupCapPascalStep {m n p q : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n)
    (hA : HasCupCapBounds A (p + 1) q)
    (hB : HasCupCapBounds B p (q + 1)) :
    ∃ P : SweptConfiguration (m + n), HasCupCapBounds P (p + 1) (q + 1) := by
  obtain ⟨P, hsplit, hleft, hright⟩ := exists_deepComposition_coloring A B
  refine ⟨P, ?_, ?_⟩
  · simpa [HasCupCapBounds] using hsplit.cap_chainSizeAtMost
      hleft hright hA.1 hB.1
  · simpa [HasCupCapBounds] using hsplit.cup_chainSizeAtMost
      hleft hright hA.2 hB.2

/-- The sharp cup--cap construction at every entry of Pascal's triangle.
It has exactly `choose (p+q) p` points, no cap larger than `p+1`, and no cup
larger than `q+1`. -/
theorem exists_cupCapExtremal (p q : ℕ) :
    ∃ P : SweptConfiguration ((p + q).choose p), HasCupCapBounds P p q := by
  induction hN : p + q using Nat.strong_induction_on generalizing p q with
  | h N ih =>
      subst N
      rcases p with _ | p
      · rw [Nat.choose_zero_right]
        exact ⟨singletonConfiguration, singleton_hasCupCapBounds 0 q⟩
      · rcases q with _ | q
        · rw [Nat.choose_self]
          exact ⟨singletonConfiguration, singleton_hasCupCapBounds (p + 1) 0⟩
        · have hleft_lt : (p + 1) + q < (p + 1) + (q + 1) := by omega
          have hright_lt : p + (q + 1) < (p + 1) + (q + 1) := by omega
          obtain ⟨A, hA⟩ := ih ((p + 1) + q) hleft_lt (p + 1) q rfl
          obtain ⟨B, hB⟩ := ih (p + (q + 1)) hright_lt p (q + 1) rfl
          obtain ⟨P, hP⟩ := exists_cupCapPascalStep A B hA hB
          have hchoose :
              Nat.choose ((p + 1) + (q + 1)) (p + 1) =
                Nat.choose ((p + 1) + q) (p + 1) +
                  Nat.choose (p + (q + 1)) p := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              Nat.choose_succ_succ' (p + q + 1) p
          rw [hchoose]
          exact ⟨P, hP⟩

/-- Sharpness in the recurrence parameters: the Pascal configuration avoids
both a cap of size `p+2` and a cup of size `q+2`. -/
theorem exists_cupCapAvoiding (p q : ℕ) :
    ∃ P : SweptConfiguration ((p + q).choose p),
      ¬ CupCap.HasCap P.tripleColoring (p + 2) ∧
      ¬ CupCap.HasCup P.tripleColoring (q + 2) := by
  obtain ⟨P, hP⟩ := exists_cupCapExtremal p q
  refine ⟨P, ?_, ?_⟩
  · rintro ⟨f, hcap⟩
    have := hP.1 hcap
    omega
  · rintro ⟨f, hcup⟩
    have := hP.2 hcup
    omega

/-- Standard-parameter sharpness half of the exact cup--cap theorem. -/
theorem exists_cupCapSharpness (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ P : SweptConfiguration ((a + b - 4).choose (a - 2)),
      ¬ CupCap.HasCap P.tripleColoring a ∧
      ¬ CupCap.HasCup P.tripleColoring b := by
  have hsum : (a - 2) + (b - 2) = a + b - 4 := by omega
  have ha' : (a - 2) + 2 = a := by omega
  have hb' : (b - 2) + 2 = b := by omega
  rw [← hsum]
  simpa [ha', hb'] using exists_cupCapAvoiding (a - 2) (b - 2)

/-- Exact cup--cap threshold: one more than the binomial coefficient always
forces the requested cap or cup, while the binomial coefficient itself is
realized by a planar configuration avoiding both. -/
theorem exact_cupCap (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∀ P : SweptConfiguration ((a + b - 4).choose (a - 2) + 1),
      CupCap.HasCap P.tripleColoring a ∨
        CupCap.HasCup P.tripleColoring b) ∧
    (∃ P : SweptConfiguration ((a + b - 4).choose (a - 2)),
      ¬ CupCap.HasCap P.tripleColoring a ∧
        ¬ CupCap.HasCup P.tripleColoring b) := by
  constructor
  · intro P
    exact CupCap.SweptConfiguration.hasCap_or_hasCup P ha hb (by omega)
  · exact exists_cupCapSharpness a b ha hb

end

end ErdosSzekeres
