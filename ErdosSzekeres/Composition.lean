import ErdosSzekeres.SmallCases

/-!
# Deep splits of sweep colorings

A deep split is the combinatorial signature of placing a left block deep below
a right block. Mixed triples with two left vertices turn left, while mixed
triples with two right vertices turn right. These are the local rules used by
the Erdős--Szekeres lower constructions.
-/

namespace ErdosSzekeres

noncomputable section

def HasDeepSplit {n : ℕ} (χ : TripleColoring n) (cut : ℕ) : Prop :=
  ∀ t : OrderedTriple n,
    (t.j.val < cut → cut ≤ t.k.val → χ t = Turn.left) ∧
    (t.i.val < cut → cut ≤ t.j.val → χ t = Turn.right)

namespace HasDeepSplit

variable {n cut : ℕ} {χ : TripleColoring n}

theorem left_left_right (hχ : HasDeepSplit χ cut)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hj : j.val < cut) (hk : cut ≤ k.val) :
    χ ⟨i, j, k, hij, hjk⟩ = Turn.left :=
  (hχ ⟨i, j, k, hij, hjk⟩).1 hj hk

theorem left_right_right (hχ : HasDeepSplit χ cut)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hi : i.val < cut) (hj : cut ≤ j.val) :
    χ ⟨i, j, k, hij, hjk⟩ = Turn.right :=
  (hχ ⟨i, j, k, hij, hjk⟩).2 hi hj

theorem cup_forbids_two_right (hχ : HasDeepSplit χ cut)
    {k : ℕ} {f : Fin k → Fin n}
    (hcup : IsCup χ f) {i j l : Fin k} (hij : i < j) (hjl : j < l)
    (hi : (f i).val < cut) (hj : cut ≤ (f j).val) : False := by
  rcases hcup with ⟨hf, hall⟩
  have hleft := hall hij hjl
  have hright := hχ.left_right_right (hf hij) (hf hjl) hi hj
  rw [hright] at hleft
  simp at hleft

theorem cap_forbids_two_left (hχ : HasDeepSplit χ cut)
    {k : ℕ} {f : Fin k → Fin n}
    (hcap : IsCap χ f) {i j l : Fin k} (hij : i < j) (hjl : j < l)
    (hj : (f j).val < cut) (hl : cut ≤ (f l).val) : False := by
  rcases hcap with ⟨hf, hall⟩
  have hright := hall hij hjl
  have hleft := hχ.left_left_right (hf hij) (hf hjl) hj hl
  rw [hleft] at hright
  simp at hright

end HasDeepSplit

theorem IsStrongPolygon.left_triple_of_right_witness
    {n cut : ℕ} {χ : TripleColoring n} (hsplit : HasDeepSplit χ cut)
    (hstrong : IsStrongPolygon χ)
    {i j k l : Fin n} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hk : k.val < cut) (hl : cut ≤ l.val) :
    χ ⟨i, j, k, hij, hjk⟩ = Turn.left := by
  have heq := (hstrong hij hjk hkl).1
  rw [HasDeepSplit.left_left_right hsplit hij (hjk.trans hkl) (by omega) hl] at heq
  exact heq

theorem IsStrongPolygon.right_triple_of_left_witness
    {n cut : ℕ} {χ : TripleColoring n} (hsplit : HasDeepSplit χ cut)
    (hstrong : IsStrongPolygon χ)
    {i j k l : Fin n} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : i.val < cut) (hj : cut ≤ j.val) :
    χ ⟨j, k, l, hjk, hkl⟩ = Turn.right := by
  have heq := (hstrong hij hjk hkl).2
  have hright := HasDeepSplit.left_right_right
    hsplit (hij.trans hjk) hkl hi (by omega)
  rw [hright] at heq
  exact heq.symm

end

end ErdosSzekeres
