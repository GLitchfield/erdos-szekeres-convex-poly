import ErdosSzekeres.Composition
import Mathlib.Data.Nat.Choose.Sum

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

/-- The strengthened Pascal invariant also controls every strong polygon in
the block. -/
def HasPascalBounds {N : ℕ} (P : SweptConfiguration N) (p q : ℕ) : Prop :=
  HasCupCapBounds P p q ∧
  StrongPolygonSizeAtMost P.tripleColoring (max 1 (p + q))

theorem singleton_hasCupCapBounds (p q : ℕ) :
    HasCupCapBounds singletonConfiguration p q := by
  constructor
  · intro k f hchain
    exact (singleton_chainSizeAtMost Turn.right hchain).trans (by omega)
  · intro k f hchain
    exact (singleton_chainSizeAtMost Turn.left hchain).trans (by omega)

theorem singleton_hasPascalBounds (p q : ℕ) :
    HasPascalBounds singletonConfiguration p q := by
  refine ⟨singleton_hasCupCapBounds p q, ?_⟩
  intro k f hstrong
  have hk : k ≤ 1 := by
    simpa using Fintype.card_le_of_injective f f.injective
  exact hk.trans (Nat.le_max_left 1 (p + q))

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

/-- Pascal composition with the additional strong-polygon invariant. -/
theorem exists_strongPascalStep {m n p q : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n)
    (hA : HasPascalBounds A (p + 1) q)
    (hB : HasPascalBounds B p (q + 1)) :
    ∃ P : SweptConfiguration (m + n), HasPascalBounds P (p + 1) (q + 1) := by
  obtain ⟨P, hsplit, hleft, hright⟩ := exists_deepComposition_coloring A B
  have hcupcap : HasCupCapBounds P (p + 1) (q + 1) := by
    constructor
    · simpa [HasCupCapBounds] using hsplit.cap_chainSizeAtMost
        hleft hright hA.1.1 hB.1.1
    · simpa [HasCupCapBounds] using hsplit.cup_chainSizeAtMost
        hleft hright hA.1.2 hB.1.2
  refine ⟨P, hcupcap, ?_⟩
  intro k f hstrong
  by_cases hleftZero : leftCount f m = 0
  · have hall : ∀ i, m ≤ (f i).val := by
      intro i
      by_contra hnot
      have hbefore : (f i).val < m := by omega
      have hi := (lt_leftCount_iff f.strictMono m i).2 hbefore
      rw [hleftZero] at hi
      omega
    have hk := strongPolygon_card_le_of_all_right hright f hstrong hall hB.2
    have hpos : 0 < p + (q + 1) := by omega
    simp [Nat.max_eq_right hpos] at hk ⊢
    omega
  · by_cases hrightZero : k - leftCount f m = 0
    · have hcount : leftCount f m = k := by
        have := leftCount_le f m
        omega
      have hall : ∀ i, (f i).val < m := by
        intro i
        rw [← lt_leftCount_iff f.strictMono m, hcount]
        exact i.isLt
      have hk := strongPolygon_card_le_of_all_left hleft f hstrong hall hA.2
      have hpos : 0 < (p + 1) + q := by omega
      simp [Nat.max_eq_right hpos] at hk ⊢
      omega
    · have husesLeft : 0 < leftCount f m := Nat.pos_of_ne_zero hleftZero
      have husesRight : 0 < k - leftCount f m := Nat.pos_of_ne_zero hrightZero
      have hk := hstrong.card_le_of_crosses_deepSplit hsplit hleft hright f
        husesLeft husesRight hA.1.2 hB.1.1
      have hpos : 0 < (p + 1) + (q + 1) := by omega
      simp [Nat.max_eq_right hpos] at hk ⊢
      omega

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

/-- Strengthened recursive Pascal block, including the optimal internal
strong-polygon bound needed when a polygon lies in a single block. -/
theorem exists_strongPascalExtremal (p q : ℕ) :
    ∃ P : SweptConfiguration ((p + q).choose p), HasPascalBounds P p q := by
  induction hN : p + q using Nat.strong_induction_on generalizing p q with
  | h N ih =>
      subst N
      rcases p with _ | p
      · rw [Nat.choose_zero_right]
        exact ⟨singletonConfiguration, singleton_hasPascalBounds 0 q⟩
      · rcases q with _ | q
        · rw [Nat.choose_self]
          exact ⟨singletonConfiguration, singleton_hasPascalBounds (p + 1) 0⟩
        · have hleft_lt : (p + 1) + q < (p + 1) + (q + 1) := by omega
          have hright_lt : p + (q + 1) < (p + 1) + (q + 1) := by omega
          obtain ⟨A, hA⟩ := ih ((p + 1) + q) hleft_lt (p + 1) q rfl
          obtain ⟨B, hB⟩ := ih (p + (q + 1)) hright_lt p (q + 1) rfl
          obtain ⟨P, hP⟩ := exists_strongPascalStep A B hA hB
          have hchoose :
              Nat.choose ((p + 1) + (q + 1)) (p + 1) =
                Nat.choose ((p + 1) + q) (p + 1) +
                  Nat.choose (p + (q + 1)) p := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              Nat.choose_succ_succ' (p + q + 1) p
          rw [hchoose]
          exact ⟨P, hP⟩

/-- Number of points in the first `t` blocks of row `d` of Pascal's
triangle. -/
def pascalRowPrefixSize (d t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, d.choose i

/-- Append block `t` to a left-associated Pascal row while preserving the
global cup and strong-polygon bounds. -/
theorem exists_pascalRowAppend {S d t : ℕ} (hd : 1 ≤ d) (ht : t ≤ d)
    (A : SweptConfiguration S)
    (hAcup : ChainSizeAtMost A.tripleColoring Turn.left t)
    (hAstrong : StrongPolygonSizeAtMost A.tripleColoring (d + 1)) :
    ∃ P : SweptConfiguration (S + d.choose t),
      ChainSizeAtMost P.tripleColoring Turn.left (t + 1) ∧
      StrongPolygonSizeAtMost P.tripleColoring (d + 1) := by
  have hchoose : Nat.choose ((d - t) + t) (d - t) = Nat.choose d t := by
    rw [Nat.sub_add_cancel ht]
    exact Nat.choose_symm ht
  have hBexists :
      ∃ B : SweptConfiguration (d.choose t), HasPascalBounds B (d - t) t := by
    rw [← hchoose]
    exact exists_strongPascalExtremal (d - t) t
  obtain ⟨B, hB⟩ := hBexists
  obtain ⟨P, hsplit, hleft, hright⟩ := exists_deepComposition_coloring A B
  refine ⟨P, ?_, ?_⟩
  · simpa using hsplit.cup_chainSizeAtMost hleft hright hAcup hB.1.2
  · intro k f hstrong
    by_cases hleftZero : leftCount f S = 0
    · have hall : ∀ i, S ≤ (f i).val := by
        intro i
        by_contra hnot
        have hbefore : (f i).val < S := by omega
        have hi := (lt_leftCount_iff f.strictMono S i).2 hbefore
        rw [hleftZero] at hi
        omega
      have hk := strongPolygon_card_le_of_all_right hright f hstrong hall hB.2
      have hmax : max 1 ((d - t) + t) = d := by
        rw [Nat.sub_add_cancel ht, Nat.max_eq_right hd]
      rw [hmax] at hk
      omega
    · by_cases hrightZero : k - leftCount f S = 0
      · have hcount : leftCount f S = k := by
          have := leftCount_le f S
          omega
        have hall : ∀ i, (f i).val < S := by
          intro i
          rw [← lt_leftCount_iff f.strictMono S, hcount]
          exact i.isLt
        exact strongPolygon_card_le_of_all_left hleft f hstrong hall hAstrong
      · have husesLeft : 0 < leftCount f S := Nat.pos_of_ne_zero hleftZero
        have husesRight : 0 < k - leftCount f S := Nat.pos_of_ne_zero hrightZero
        have hk := hstrong.card_le_of_crosses_deepSplit hsplit hleft hright f
          husesLeft husesRight hAcup hB.1.1
        omega

/-- Every nonempty prefix of a Pascal row has a genuine planar realization.
The first `t` blocks have cup bound `t` and avoid strong polygons larger than
`d+1`. -/
theorem exists_pascalRowPrefix (d t : ℕ) (hd : 1 ≤ d)
    (htpos : 1 ≤ t) (htop : t ≤ d + 1) :
    ∃ P : SweptConfiguration (pascalRowPrefixSize d t),
      ChainSizeAtMost P.tripleColoring Turn.left t ∧
      StrongPolygonSizeAtMost P.tripleColoring (d + 1) := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases htzero : t = 0
      · subst t
        have hsize : pascalRowPrefixSize d 1 = 1 := by
          simp [pascalRowPrefixSize]
        rw [hsize]
        refine ⟨singletonConfiguration, ?_, ?_⟩
        · exact singleton_chainSizeAtMost Turn.left
        · intro k f hstrong
          have hk : k ≤ 1 := by
            simpa using Fintype.card_le_of_injective f f.injective
          omega
      · have htpos' : 1 ≤ t := Nat.one_le_iff_ne_zero.2 htzero
        have htop' : t ≤ d + 1 := by omega
        obtain ⟨A, hAcup, hAstrong⟩ := ih htpos' htop'
        have ht : t ≤ d := by omega
        obtain ⟨P, hPcup, hPstrong⟩ :=
          exists_pascalRowAppend hd ht A hAcup hAstrong
        have hsize : pascalRowPrefixSize d (t + 1) =
            pascalRowPrefixSize d t + d.choose t := by
          simp [pascalRowPrefixSize, Finset.sum_range_succ]
        rw [hsize]
        exact ⟨P, hPcup, hPstrong⟩

/-- The complete Pascal row has `2^d` planar points and no strong polygon
larger than `d+1`. -/
theorem exists_pascalRow (d : ℕ) (hd : 1 ≤ d) :
    ∃ P : SweptConfiguration (2 ^ d),
      StrongPolygonSizeAtMost P.tripleColoring (d + 1) := by
  obtain ⟨P, _, hstrong⟩ :=
    exists_pascalRowPrefix d (d + 1) hd (by omega) (by omega)
  have hsize : pascalRowPrefixSize d (d + 1) = 2 ^ d := by
    exact Nat.sum_range_choose d
  rw [← hsize]
  exact ⟨P, hstrong⟩

/-- A strong-polygon bound on a swept configuration rules out a larger
convex subset of its underlying planar point set. -/
theorem SweptConfiguration.not_containsConvexSubset_of_strongBound
    {N bound target : ℕ} (P : SweptConfiguration N)
    (hbound : StrongPolygonSizeAtMost P.tripleColoring bound)
    (hlt : bound < target) : ¬ ContainsConvexSubset P.pointFinset target := by
  classical
  rintro ⟨t, hts, htcard, htconvex⟩
  have hts' : t ⊆ Finset.univ.image P.point := by
    simpa [SweptConfiguration.pointFinset] using hts
  obtain ⟨u, hu⟩ := Finset.subset_univ_image_iff.mp hts'
  have hucard : u.card = target := by
    calc
      u.card = (u.image P.point).card :=
        (Finset.card_image_of_injective u P.point_injective).symm
      _ = t.card := congrArg Finset.card hu
      _ = target := htcard
  let f : Fin target ↪o Fin N := u.orderEmbOfFin hucard
  have hselected : (P.restrict f).pointFinset = t := by
    calc
      (P.restrict f).pointFinset =
          (Finset.univ.image f).image P.point := by
        rw [SweptConfiguration.pointFinset, Finset.image_image]
        rfl
      _ = u.image P.point := by
        rw [Finset.image_orderEmbOfFin_univ]
      _ = t := hu
  have hstrongRestricted : IsStrongPolygon (P.restrict f).tripleColoring :=
    (P.restrict f).inConvexPosition_pointFinset_iff_isStrongPolygon.mp
      (hselected ▸ htconvex)
  have hstrong : IsStrongPolygonOn P.tripleColoring f := by
    rw [IsStrongPolygonOn, ← P.restrict_tripleColoring f]
    exact hstrongRestricted
  have := hbound f hstrong
  omega

/-- D4: the classical all-`n` lower construction, as an actual planar
sharpness witness of size `2^(n-2)`. -/
theorem classical_lower_sharpness (n : ℕ) (hn : 3 ≤ n) :
    HasSharpnessExample n (2 ^ (n - 2) + 1) := by
  have hd : 1 ≤ n - 2 := by omega
  obtain ⟨P, hstrong⟩ := exists_pascalRow (n - 2) hd
  refine ⟨P.pointFinset, ?_, P.pointFinset_generalPosition, ?_⟩
  · simp
  · apply P.not_containsConvexSubset_of_strongBound hstrong
    omega

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
