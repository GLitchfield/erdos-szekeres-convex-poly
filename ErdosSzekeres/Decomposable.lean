module

public import ErdosSzekeres.Extremal
public import ErdosSzekeres.CupCap
public import ErdosSzekeres.SmallCases
public import ErdosSzekeres.ES5CNFGenerated
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Decomposable point configurations

This file formalizes the recursive class used by Baek and Balko in their
proof of the Erdős--Szekeres conjecture for decomposable point sets.  Unlike
`HasDeepSplit`, the two parts of a deep-below partition need not be contiguous
in sweep order.
-/

namespace ErdosSzekeres

noncomputable section

/-- Every increasing triple selected from `s` turns left. -/
def IsCupSet {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n)) : Prop :=
  ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = Turn.left

/-- Every increasing triple selected from `s` turns right. -/
def IsCapSet {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n)) : Prop :=
  ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = Turn.right

/-- The four-index strong-polygon law, restricted to an ambient index set. -/
def IsStrongPolygonSet {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) : Prop :=
  ∀ ⦃i j k l : Fin n⦄, (hij : i < j) → (hjk : j < k) → (hkl : k < l) →
    i ∈ s → j ∈ s → k ∈ s → l ∈ s →
    χ ⟨i, j, k, hij, hjk⟩ =
        χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
      χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
        χ ⟨j, k, l, hjk, hkl⟩

/-- A cup of prescribed cardinality contained in `s`. -/
def ContainsCupSet {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) (u : ℕ) : Prop :=
  ∃ cup : Finset (Fin n), cup ⊆ s ∧ cup.card = u ∧ IsCupSet χ cup

/-- A cap of prescribed cardinality contained in `s`. -/
def ContainsCapSet {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) (a : ℕ) : Prop :=
  ∃ cap : Finset (Fin n), cap ⊆ s ∧ cap.card = a ∧ IsCapSet χ cap

/-- A strong polygon of prescribed cardinality contained in `s`. -/
def ContainsStrongPolygonSet {n : ℕ} (χ : TripleColoring n)
    (s : Finset (Fin n)) (k : ℕ) : Prop :=
  ∃ polygon : Finset (Fin n), polygon ⊆ s ∧ polygon.card = k ∧
    IsStrongPolygonSet χ polygon

namespace FinsetPolygon

variable {n : ℕ} {χ : TripleColoring n} {s t : Finset (Fin n)}

theorem IsCupSet.mono (h : IsCupSet χ s) (hts : t ⊆ s) :
    IsCupSet χ t := by
  intro triple hi hj hk
  exact h triple (hts hi) (hts hj) (hts hk)

theorem IsCapSet.mono (h : IsCapSet χ s) (hts : t ⊆ s) :
    IsCapSet χ t := by
  intro triple hi hj hk
  exact h triple (hts hi) (hts hj) (hts hk)

theorem IsStrongPolygonSet.mono (h : IsStrongPolygonSet χ s)
    (hts : t ⊆ s) : IsStrongPolygonSet χ t := by
  intro i j k l hij hjk hkl hi hj hk hl
  exact h hij hjk hkl (hts hi) (hts hj) (hts hk) (hts hl)

theorem IsCupSet.isStrongPolygonSet (h : IsCupSet χ s) :
    IsStrongPolygonSet χ s := by
  intro i j k l hij hjk hkl hi hj hk hl
  constructor
  · rw [h ⟨i, j, k, hij, hjk⟩ hi hj hk,
      h ⟨i, j, l, hij, hjk.trans hkl⟩ hi hj hl]
  · rw [h ⟨i, k, l, hij.trans hjk, hkl⟩ hi hk hl,
      h ⟨j, k, l, hjk, hkl⟩ hj hk hl]

theorem IsCapSet.isStrongPolygonSet (h : IsCapSet χ s) :
    IsStrongPolygonSet χ s := by
  intro i j k l hij hjk hkl hi hj hk hl
  constructor
  · rw [h ⟨i, j, k, hij, hjk⟩ hi hj hk,
      h ⟨i, j, l, hij, hjk.trans hkl⟩ hi hj hl]
  · rw [h ⟨i, k, l, hij.trans hjk, hkl⟩ hi hk hl,
      h ⟨j, k, l, hjk, hkl⟩ hj hk hl]

theorem IsCupSet.isCup_orderEmbOfFin (h : IsCupSet χ s) :
    IsCup χ (s.orderEmbOfFin rfl) := by
  refine ⟨(s.orderEmbOfFin rfl).strictMono, ?_⟩
  intro i j k hij hjk
  exact h _ (s.orderEmbOfFin_mem rfl i)
    (s.orderEmbOfFin_mem rfl j) (s.orderEmbOfFin_mem rfl k)

theorem IsCapSet.isCap_orderEmbOfFin (h : IsCapSet χ s) :
    IsCap χ (s.orderEmbOfFin rfl) := by
  refine ⟨(s.orderEmbOfFin rfl).strictMono, ?_⟩
  intro i j k hij hjk
  exact h _ (s.orderEmbOfFin_mem rfl i)
    (s.orderEmbOfFin_mem rfl j) (s.orderEmbOfFin_mem rfl k)

theorem IsStrongPolygonSet.isStrongPolygonOn_orderEmbOfFin
    (h : IsStrongPolygonSet χ s) :
    IsStrongPolygonOn χ (s.orderEmbOfFin rfl) := by
  intro i j k l hij hjk hkl
  exact h ((s.orderEmbOfFin rfl).strictMono hij)
    ((s.orderEmbOfFin rfl).strictMono hjk)
    ((s.orderEmbOfFin rfl).strictMono hkl)
    (s.orderEmbOfFin_mem rfl i) (s.orderEmbOfFin_mem rfl j)
    (s.orderEmbOfFin_mem rfl k) (s.orderEmbOfFin_mem rfl l)

theorem IsStrongPolygonOn.isStrongPolygonSet_image
    {k : ℕ} {f : Fin k ↪o Fin n} (h : IsStrongPolygonOn χ f) :
    IsStrongPolygonSet χ (Finset.univ.image f) := by
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi hj hk hl
  obtain ⟨a, rfl⟩ := hi
  obtain ⟨b, rfl⟩ := hj
  obtain ⟨c, rfl⟩ := hk
  obtain ⟨d, rfl⟩ := hl
  exact h (f.lt_iff_lt.mp hij) (f.lt_iff_lt.mp hjk) (f.lt_iff_lt.mp hkl)

theorem IsMonochromaticChain.isMonochromaticSet_image
    {k : ℕ} {c : Turn} {f : Fin k ↪o Fin n}
    (h : IsMonochromaticChain χ c f) :
    ∀ t : OrderedTriple n, t.i ∈ Finset.univ.image f →
      t.j ∈ Finset.univ.image f → t.k ∈ Finset.univ.image f → χ t = c := by
  rcases h with ⟨hf, hall⟩
  intro t hi hj hk
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi hj hk
  obtain ⟨i, hi⟩ := hi
  obtain ⟨j, hj⟩ := hj
  obtain ⟨k, hk⟩ := hk
  have hfij : f i < f j := by simpa [hi, hj] using t.hij
  have hfjk : f j < f k := by simpa [hj, hk] using t.hjk
  have hij : i < j := f.lt_iff_lt.mp hfij
  have hjk : j < k := f.lt_iff_lt.mp hfjk
  have ht : t = ⟨f i, f j, f k, f.strictMono hij, f.strictMono hjk⟩ := by
    cases t
    simp_all
  rw [ht]
  exact hall hij hjk

theorem IsCup.image {k : ℕ} {f : Fin k ↪o Fin n} (h : IsCup χ f) :
    IsCupSet χ (Finset.univ.image f) :=
  IsMonochromaticChain.isMonochromaticSet_image h

theorem IsCap.image {k : ℕ} {f : Fin k ↪o Fin n} (h : IsCap χ f) :
    IsCapSet χ (Finset.univ.image f) :=
  IsMonochromaticChain.isMonochromaticSet_image h

theorem ContainsCupSet.mono (h : ContainsCupSet χ t u) (hts : t ⊆ s) :
    ContainsCupSet χ s u := by
  obtain ⟨cup, hcup, hcard, hmono⟩ := h
  exact ⟨cup, hcup.trans hts, hcard, hmono⟩

theorem ContainsCapSet.mono (h : ContainsCapSet χ t a) (hts : t ⊆ s) :
    ContainsCapSet χ s a := by
  obtain ⟨cap, hcap, hcard, hmono⟩ := h
  exact ⟨cap, hcap.trans hts, hcard, hmono⟩

theorem ContainsStrongPolygonSet.mono
    (h : ContainsStrongPolygonSet χ t k) (hts : t ⊆ s) :
    ContainsStrongPolygonSet χ s k := by
  obtain ⟨polygon, hpolygon, hcard, hstrong⟩ := h
  exact ⟨polygon, hpolygon.trans hts, hcard, hstrong⟩

theorem ContainsCupSet.toContainsStrongPolygonSet
    (h : ContainsCupSet χ s k) : ContainsStrongPolygonSet χ s k := by
  obtain ⟨cup, hcup, hcard, hmono⟩ := h
  exact ⟨cup, hcup, hcard, IsCupSet.isStrongPolygonSet hmono⟩

theorem ContainsCapSet.toContainsStrongPolygonSet
    (h : ContainsCapSet χ s k) : ContainsStrongPolygonSet χ s k := by
  obtain ⟨cap, hcap, hcard, hmono⟩ := h
  exact ⟨cap, hcap, hcard, IsCapSet.isStrongPolygonSet hmono⟩

end FinsetPolygon

/-- The Pascal-row window occurring in the active three-parameter regime. -/
def decomposableBinomialWindow (a u k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc (k - a) (u - 2), Nat.choose (k - 2) j

/-- Baek--Balko's three-parameter extremal threshold.  When the convex-polygon
parameter is inactive this is the classical cup--cap binomial coefficient;
otherwise it is the indicated window in row `k-2` of Pascal's triangle. -/
def decomposableThreshold (a u k : ℕ) : ℕ :=
  if a = 1 ∨ u = 1 then 0
  else if a + u ≤ k + 3 then Nat.choose (a + u - 4) (a - 2)
  else decomposableBinomialWindow a u k

@[simp] theorem decomposableThreshold_one_left (u k : ℕ) :
    decomposableThreshold 1 u k = 0 := by
  simp [decomposableThreshold]

@[simp] theorem decomposableThreshold_one_right (a k : ℕ) :
    decomposableThreshold a 1 k = 0 := by
  simp [decomposableThreshold]

theorem decomposableThreshold_eq_choose {a u k : ℕ}
    (ha : 2 ≤ a) (hu : 2 ≤ u) (hbase : a + u ≤ k + 3) :
    decomposableThreshold a u k = Nat.choose (a + u - 4) (a - 2) := by
  rw [decomposableThreshold, if_neg (by omega), if_pos hbase]

theorem decomposableThreshold_eq_window {a u k : ℕ}
    (ha : 2 ≤ a) (hu : 2 ≤ u) (hactive : k + 4 ≤ a + u) :
    decomposableThreshold a u k = decomposableBinomialWindow a u k := by
  rw [decomposableThreshold, if_neg (by omega), if_neg (by omega)]

/-- On the diagonal, the threshold is the full binomial row. -/
theorem decomposableThreshold_diagonal (k : ℕ) (hk : 3 ≤ k) :
    decomposableThreshold k k k = 2 ^ (k - 2) := by
  by_cases hk3 : k = 3
  · subst k
    norm_num [decomposableThreshold]
  · have hk4 : 4 ≤ k := by omega
    have hnotOne : ¬(k = 1 ∨ k = 1) := by omega
    have hnotBase : ¬k + k ≤ k + 3 := by omega
    rw [decomposableThreshold, if_neg hnotOne, if_neg hnotBase]
    have hinterval : Finset.Icc (k - k) (k - 2) = Finset.range (k - 2 + 1) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [decomposableBinomialWindow, hinterval]
    exact Nat.sum_range_choose (k - 2)

/-- A kernel-checked boundary regression for the published three-parameter
induction.  At `(a,u,k) = (4,5,5)`, taking the auxiliary parameters
`u' = 1` and `a' = 3` satisfies `a' + u' <= k - 1`, but the two advertised
cardinality contributions sum to eight rather than at most the threshold
seven.  Any formal proof of the diagonal theorem must therefore strengthen
the induction invariant or handle this boundary separately. -/
theorem published_induction_boundary_regression :
    decomposableThreshold 4 1 5 + Nat.choose 3 0 +
        decomposableThreshold 3 5 5 + Nat.choose 3 2 = 8 ∧
      decomposableThreshold 4 5 5 = 7 ∧
      ¬decomposableThreshold 4 1 5 + Nat.choose 3 0 +
          decomposableThreshold 3 5 5 + Nat.choose 3 2 ≤
        decomposableThreshold 4 5 5 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow,
    Finset.sum_Icc_succ_top]

/-- In the interior range, the two Pascal windows from the published
induction are disjoint subintervals of the outer window.  The hypothesis
`k-a+1 <= u'` isolates the lower endpoint condition missing in the boundary
regression above; the dual representation supplies its symmetric condition. -/
theorem decomposableBinomialWindow_pair_le
    {a u k a' u' : ℕ} (ha : a ≤ k) (hu : u ≤ k)
    (ha' : a' < a) (hu' : u' < u) (hsum : a' + u' ≤ k - 1)
    (hu'Lower : k - a + 1 ≤ u') :
    decomposableBinomialWindow a (u' + 1) k +
        decomposableBinomialWindow (a' + 1) u k ≤
      decomposableBinomialWindow a u k := by
  let first := Finset.Icc (k - a) (u' + 1 - 2)
  let second := Finset.Icc (k - (a' + 1)) (u - 2)
  let outer := Finset.Icc (k - a) (u - 2)
  have hdisjoint : Disjoint first second := by
    rw [Finset.disjoint_left]
    intro j hjFirst hjSecond
    simp only [first, second, Finset.mem_Icc] at hjFirst hjSecond
    omega
  have hsubset : first ∪ second ⊆ outer := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjFirst | hjSecond
    · simp only [first, Finset.mem_Icc] at hjFirst
      simp only [outer, Finset.mem_Icc]
      omega
    · simp only [second, Finset.mem_Icc] at hjSecond
      simp only [outer, Finset.mem_Icc]
      omega
  change (∑ j ∈ first, Nat.choose (k - 2) j) +
      (∑ j ∈ second, Nat.choose (k - 2) j) ≤
    ∑ j ∈ outer, Nat.choose (k - 2) j
  rw [← Finset.sum_union hdisjoint]
  exact Finset.sum_le_sum_of_subset hsubset

/-- The Pascal-window absorption used at the outer diagonal of E3 is valid.
The boundary defect in `published_induction_boundary_regression` can only be
encountered after descending to an off-diagonal induction state: on the
diagonal the lower endpoint condition is automatic for every positive
auxiliary cup parameter. -/
theorem decomposableBinomialWindow_diagonal_pair_le
    {k a' u' : ℕ} (ha' : a' < k) (hu' : u' < k)
    (hsum : a' + u' ≤ k - 1) (hu'Pos : 1 ≤ u') :
    decomposableBinomialWindow k (u' + 1) k +
        decomposableBinomialWindow (a' + 1) k k ≤
      decomposableBinomialWindow k k k := by
  exact decomposableBinomialWindow_pair_le (a := k) (u := k)
    (by rfl) (by rfl) ha' hu' hsum (by simpa using hu'Pos)

/-- The ordinary cup--cap theorem, localized to an arbitrary finite set of
indices in a sweep-realizable coloring. -/
theorem containsCapSet_or_containsCupSet_of_choose_lt
    {n a u : ℕ} {χ : TripleColoring n} (hχ : IsSweepRealizable χ)
    (s : Finset (Fin n)) (ha : 2 ≤ a) (hu : 2 ≤ u)
    (hcard : Nat.choose (a + u - 4) (a - 2) < s.card) :
    ContainsCapSet χ s a ∨ ContainsCupSet χ s u := by
  obtain ⟨P, rfl⟩ := hχ
  let e : Fin s.card ↪o Fin n := s.orderEmbOfFin rfl
  have hrestricted : Nat.choose (a + u - 4) (a - 2) <
      Fintype.card (Fin s.card) := by simpa using hcard
  rcases CupCap.SweptConfiguration.hasCap_or_hasCup
      (P.restrict e) ha hu (by simpa using hrestricted) with
      ⟨f, hcap⟩ | ⟨f, hcup⟩
  · let g : Fin a ↪o Fin n := f.trans e
    let cap := Finset.univ.image g
    refine Or.inl ⟨cap, ?_, ?_, ?_⟩
    · intro x hx
      simp only [cap, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact s.orderEmbOfFin_mem rfl (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCap P.tripleColoring g :=
        IsMonochromaticChain.map_of_restrict_eq e
          (P.restrict_tripleColoring e).symm hcap
      exact FinsetPolygon.IsCap.image hmap
  · let g : Fin u ↪o Fin n := f.trans e
    let cup := Finset.univ.image g
    refine Or.inr ⟨cup, ?_, ?_, ?_⟩
    · intro x hx
      simp only [cup, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact s.orderEmbOfFin_mem rfl (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCup P.tripleColoring g :=
        IsMonochromaticChain.map_of_restrict_eq e
          (P.restrict_tripleColoring e).symm hcup
      exact FinsetPolygon.IsCup.image hmap

/-- Combinatorial orientation law of a deep-below partition.  For a crossing
triple, the turn is left exactly when its middle vertex lies in the lower
part.  This formulation remains valid when the parts interleave in sweep
order. -/
structure HasDeepBelowSplit {n : ℕ} (χ : TripleColoring n)
    (lower upper : Finset (Fin n)) : Prop where
  disjoint : Disjoint lower upper
  crossing : ∀ t : OrderedTriple n,
    t.i ∈ lower ∪ upper → t.j ∈ lower ∪ upper → t.k ∈ lower ∪ upper →
    ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) →
    ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) →
    χ t = if t.j ∈ lower then Turn.left else Turn.right

namespace HasDeepBelowSplit

variable {n : ℕ} {χ : TripleColoring n}
  {lower upper : Finset (Fin n)}

set_option maxHeartbeats 1000000 in
/-- A four-set crossing a deep-below split satisfies the rank-three
one-change law.  This is the local combinatorial reason recursive deep-below
colorings remain signotopes even without a geometric realizability witness. -/
theorem turnSequenceAllowed_of_crossing_four
    (h : HasDeepBelowSplit χ lower upper)
    {i j k l : Fin n} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : i ∈ lower ∪ upper) (hj : j ∈ lower ∪ upper)
    (hk : k ∈ lower ∪ upper) (hl : l ∈ lower ∪ upper)
    (hnotLower : ¬(i ∈ lower ∧ j ∈ lower ∧ k ∈ lower ∧ l ∈ lower))
    (hnotUpper : ¬(i ∈ upper ∧ j ∈ upper ∧ k ∈ upper ∧ l ∈ upper)) :
    TurnSequenceAllowed
      (χ ⟨i, j, k, hij, hjk⟩)
      (χ ⟨i, j, l, hij, hjk.trans hkl⟩)
      (χ ⟨i, k, l, hij.trans hjk, hkl⟩)
      (χ ⟨j, k, l, hjk, hkl⟩) := by
  have hijk :
      ¬(i ∈ lower ∧ j ∈ lower ∧ k ∈ lower) →
      ¬(i ∈ upper ∧ j ∈ upper ∧ k ∈ upper) →
      χ ⟨i, j, k, hij, hjk⟩ =
        if j ∈ lower then Turn.left else Turn.right := by
    exact fun hLower hUpper => h.crossing _ hi hj hk hLower hUpper
  have hijl :
      ¬(i ∈ lower ∧ j ∈ lower ∧ l ∈ lower) →
      ¬(i ∈ upper ∧ j ∈ upper ∧ l ∈ upper) →
      χ ⟨i, j, l, hij, hjk.trans hkl⟩ =
        if j ∈ lower then Turn.left else Turn.right := by
    exact fun hLower hUpper => h.crossing _ hi hj hl hLower hUpper
  have hikl :
      ¬(i ∈ lower ∧ k ∈ lower ∧ l ∈ lower) →
      ¬(i ∈ upper ∧ k ∈ upper ∧ l ∈ upper) →
      χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
        if k ∈ lower then Turn.left else Turn.right := by
    exact fun hLower hUpper => h.crossing _ hi hk hl hLower hUpper
  have hjkl :
      ¬(j ∈ lower ∧ k ∈ lower ∧ l ∈ lower) →
      ¬(j ∈ upper ∧ k ∈ upper ∧ l ∈ upper) →
      χ ⟨j, k, l, hjk, hkl⟩ =
        if k ∈ lower then Turn.left else Turn.right := by
    exact fun hLower hUpper => h.crossing _ hj hk hl hLower hUpper
  have hdisjoint := Finset.disjoint_left.mp h.disjoint
  have hdisjoint' := Finset.disjoint_left.mp h.disjoint.symm
  rcases Finset.mem_union.mp hi with hiLower | hiUpper <;>
    rcases Finset.mem_union.mp hj with hjLower | hjUpper <;>
      rcases Finset.mem_union.mp hk with hkLower | hkUpper <;>
        rcases Finset.mem_union.mp hl with hlLower | hlUpper <;>
          cases h₀ : χ ⟨i, j, k, hij, hjk⟩ <;>
            cases h₁ : χ ⟨i, j, l, hij, hjk.trans hkl⟩ <;>
              cases h₂ : χ ⟨i, k, l, hij.trans hjk, hkl⟩ <;>
                cases h₃ : χ ⟨j, k, l, hjk, hkl⟩ <;>
                  simp_all [TurnSequenceAllowed]

/-- Membership at one of the two sweep extremes of a finite index set. -/
def IsLeftSweepEndpoint (s : Finset (Fin n)) (q : Fin n) : Prop :=
  ∀ x ∈ s, q ≤ x

/-- Membership at the right sweep extreme of a finite index set. -/
def IsRightSweepEndpoint (s : Finset (Fin n)) (q : Fin n) : Prop :=
  ∀ x ∈ s, x ≤ q

/-- Being a sweep endpoint is the disjunction of the two directional states. -/
def IsSweepEndpoint (s : Finset (Fin n)) (q : Fin n) : Prop :=
  IsLeftSweepEndpoint s q ∨ IsRightSweepEndpoint s q

theorem isSweepEndpoint_iff (s : Finset (Fin n)) (q : Fin n) :
    IsSweepEndpoint s q ↔
      (∀ x ∈ s, q ≤ x) ∨ (∀ x ∈ s, x ≤ q) := by
  rfl

/-- A point outside a nonempty finite set cannot be both its left and its
right sweep endpoint.  Thus the endpoint flag carried by a genuine crossing
extension is a binary, not overlapping, state. -/
theorem not_isLeft_and_isRightSweepEndpoint
    {s : Finset (Fin n)} {q : Fin n} (hs : s.Nonempty) (hq : q ∉ s) :
    ¬(IsLeftSweepEndpoint s q ∧ IsRightSweepEndpoint s q) := by
  rintro ⟨hleft, hright⟩
  obtain ⟨x, hx⟩ := hs
  have hxq : x = q := le_antisymm (hright x hx) (hleft x hx)
  exact hq (hxq ▸ hx)

/-- Negating the endpoint state says exactly that the set has witnesses on
both sides of the point. -/
theorem not_isSweepEndpoint_iff_exists_lt_and_exists_gt
    (s : Finset (Fin n)) (q : Fin n) :
    ¬ IsSweepEndpoint s q ↔
      (∃ x ∈ s, x < q) ∧ ∃ y ∈ s, q < y := by
  simp [IsSweepEndpoint, IsLeftSweepEndpoint, IsRightSweepEndpoint,
    not_or, not_le]

/-- A vertex from the upper block extends a lower-block cup on its left. -/
theorem insert_upper_isCupSet_of_isLeftSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)}
    (hcupSub : cup ⊆ lower) (hcup : IsCupSet χ cup) {q : Fin n}
    (hqUpper : q ∈ upper) (hqLeft : IsLeftSweepEndpoint cup q) :
    IsCupSet χ (insert q cup) := by
  intro t hi hj hk
  rcases Finset.mem_insert.mp hi with hiq | hiCup
  · have hjq : t.j ≠ q := by
      intro hjq
      exact (ne_of_lt t.hij) (hiq.trans hjq.symm)
    have hkq : t.k ≠ q := by
      intro hkq
      exact (ne_of_lt (t.hij.trans t.hjk)) (hiq.trans hkq.symm)
    have hjCup := (Finset.mem_insert.mp hj).resolve_left hjq
    have hkCup := (Finset.mem_insert.mp hk).resolve_left hkq
    have hiUpper : t.i ∈ upper := hiq ▸ hqUpper
    have hjLower := hcupSub hjCup
    have hkLower := hcupSub hkCup
    have hdisj := Finset.disjoint_left.mp h.disjoint
    have hiNotLower : t.i ∉ lower := fun hiLower => hdisj hiLower hiUpper
    have hjNotUpper : t.j ∉ upper := fun hjUpper => hdisj hjLower hjUpper
    have hkNotUpper : t.k ∉ upper := fun hkUpper => hdisj hkLower hkUpper
    simpa [hiNotLower, hjLower] using h.crossing t
      (Finset.mem_union_right _ hiUpper)
      (Finset.mem_union_left _ hjLower)
      (Finset.mem_union_left _ hkLower)
      (by simp [hiNotLower]) (by simp [hjNotUpper, hkNotUpper])
  · have hqle : q ≤ t.i := hqLeft t.i hiCup
    have hjq : t.j ≠ q := by
      intro hjq
      have : t.j ≤ t.i := by simpa [hjq] using hqle
      exact (not_le_of_gt t.hij) this
    have hkq : t.k ≠ q := by
      intro hkq
      have : t.k ≤ t.i := by simpa [hkq] using hqle
      exact (not_le_of_gt (t.hij.trans t.hjk)) this
    have hjCup := (Finset.mem_insert.mp hj).resolve_left hjq
    have hkCup := (Finset.mem_insert.mp hk).resolve_left hkq
    exact hcup t hiCup hjCup hkCup

/-- A vertex from the upper block extends a lower-block cup on its right. -/
theorem insert_upper_isCupSet_of_isRightSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)}
    (hcupSub : cup ⊆ lower) (hcup : IsCupSet χ cup) {q : Fin n}
    (hqUpper : q ∈ upper) (hqRight : IsRightSweepEndpoint cup q) :
    IsCupSet χ (insert q cup) := by
  intro t hi hj hk
  rcases Finset.mem_insert.mp hk with hkq | hkCup
  · have hiq : t.i ≠ q := by
      intro hiq
      exact (ne_of_lt (t.hij.trans t.hjk)) (hiq.trans hkq.symm)
    have hjq : t.j ≠ q := by
      intro hjq
      exact (ne_of_lt t.hjk) (hjq.trans hkq.symm)
    have hiCup := (Finset.mem_insert.mp hi).resolve_left hiq
    have hjCup := (Finset.mem_insert.mp hj).resolve_left hjq
    have hiLower := hcupSub hiCup
    have hjLower := hcupSub hjCup
    have hkUpper : t.k ∈ upper := hkq ▸ hqUpper
    have hdisj := Finset.disjoint_left.mp h.disjoint
    have hiNotUpper : t.i ∉ upper := fun hiUpper => hdisj hiLower hiUpper
    have hjNotUpper : t.j ∉ upper := fun hjUpper => hdisj hjLower hjUpper
    have hkNotLower : t.k ∉ lower := fun hkLower => hdisj hkLower hkUpper
    simpa [hjLower, hkNotLower] using h.crossing t
      (Finset.mem_union_left _ hiLower)
      (Finset.mem_union_left _ hjLower)
      (Finset.mem_union_right _ hkUpper)
      (by simp [hkNotLower]) (by simp [hiNotUpper, hjNotUpper])
  · have hkle : t.k ≤ q := hqRight t.k hkCup
    have hiq : t.i ≠ q := by
      intro hiq
      have : t.k ≤ t.i := by simpa [hiq] using hkle
      exact (not_le_of_gt (t.hij.trans t.hjk)) this
    have hjq : t.j ≠ q := by
      intro hjq
      have : t.k ≤ t.j := by simpa [hjq] using hkle
      exact (not_le_of_gt t.hjk) this
    have hiCup := (Finset.mem_insert.mp hi).resolve_left hiq
    have hjCup := (Finset.mem_insert.mp hj).resolve_left hjq
    exact hcup t hiCup hjCup hkCup

/-- Dually, a vertex from the lower block extends an upper-block cap on its
left. -/
theorem insert_lower_isCapSet_of_isLeftSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)}
    (hcapSub : cap ⊆ upper) (hcap : IsCapSet χ cap) {q : Fin n}
    (hqLower : q ∈ lower) (hqLeft : IsLeftSweepEndpoint cap q) :
    IsCapSet χ (insert q cap) := by
  intro t hi hj hk
  rcases Finset.mem_insert.mp hi with hiq | hiCap
  · have hjq : t.j ≠ q := by
      intro hjq
      exact (ne_of_lt t.hij) (hiq.trans hjq.symm)
    have hkq : t.k ≠ q := by
      intro hkq
      exact (ne_of_lt (t.hij.trans t.hjk)) (hiq.trans hkq.symm)
    have hjCap := (Finset.mem_insert.mp hj).resolve_left hjq
    have hkCap := (Finset.mem_insert.mp hk).resolve_left hkq
    have hiLower : t.i ∈ lower := hiq ▸ hqLower
    have hjUpper := hcapSub hjCap
    have hkUpper := hcapSub hkCap
    have hdisj := Finset.disjoint_left.mp h.disjoint
    have hiNotUpper : t.i ∉ upper := fun hiUpper => hdisj hiLower hiUpper
    have hjNotLower : t.j ∉ lower := fun hjLower => hdisj hjLower hjUpper
    have hkNotLower : t.k ∉ lower := fun hkLower => hdisj hkLower hkUpper
    simpa [hjNotLower] using h.crossing t
      (Finset.mem_union_left _ hiLower)
      (Finset.mem_union_right _ hjUpper)
      (Finset.mem_union_right _ hkUpper)
      (by simp [hjNotLower, hkNotLower]) (by simp [hiNotUpper])
  · have hqle : q ≤ t.i := hqLeft t.i hiCap
    have hjq : t.j ≠ q := by
      intro hjq
      have : t.j ≤ t.i := by simpa [hjq] using hqle
      exact (not_le_of_gt t.hij) this
    have hkq : t.k ≠ q := by
      intro hkq
      have : t.k ≤ t.i := by simpa [hkq] using hqle
      exact (not_le_of_gt (t.hij.trans t.hjk)) this
    have hjCap := (Finset.mem_insert.mp hj).resolve_left hjq
    have hkCap := (Finset.mem_insert.mp hk).resolve_left hkq
    exact hcap t hiCap hjCap hkCap

/-- A vertex from the lower block extends an upper-block cap on its right. -/
theorem insert_lower_isCapSet_of_isRightSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)}
    (hcapSub : cap ⊆ upper) (hcap : IsCapSet χ cap) {q : Fin n}
    (hqLower : q ∈ lower) (hqRight : IsRightSweepEndpoint cap q) :
    IsCapSet χ (insert q cap) := by
  intro t hi hj hk
  rcases Finset.mem_insert.mp hk with hkq | hkCap
  · have hiq : t.i ≠ q := by
      intro hiq
      exact (ne_of_lt (t.hij.trans t.hjk)) (hiq.trans hkq.symm)
    have hjq : t.j ≠ q := by
      intro hjq
      exact (ne_of_lt t.hjk) (hjq.trans hkq.symm)
    have hiCap := (Finset.mem_insert.mp hi).resolve_left hiq
    have hjCap := (Finset.mem_insert.mp hj).resolve_left hjq
    have hiUpper := hcapSub hiCap
    have hjUpper := hcapSub hjCap
    have hkLower : t.k ∈ lower := hkq ▸ hqLower
    have hdisj := Finset.disjoint_left.mp h.disjoint
    have hiNotLower : t.i ∉ lower := fun hiLower => hdisj hiLower hiUpper
    have hjNotLower : t.j ∉ lower := fun hjLower => hdisj hjLower hjUpper
    have hkNotUpper : t.k ∉ upper := fun hkUpper => hdisj hkLower hkUpper
    simpa [hjNotLower] using h.crossing t
      (Finset.mem_union_right _ hiUpper)
      (Finset.mem_union_right _ hjUpper)
      (Finset.mem_union_left _ hkLower)
      (by simp [hiNotLower, hjNotLower]) (by simp [hkNotUpper])
  · have hkle : t.k ≤ q := hqRight t.k hkCap
    have hiq : t.i ≠ q := by
      intro hiq
      have : t.k ≤ t.i := by simpa [hiq] using hkle
      exact (not_le_of_gt (t.hij.trans t.hjk)) this
    have hjq : t.j ≠ q := by
      intro hjq
      have : t.k ≤ t.j := by simpa [hjq] using hkle
      exact (not_le_of_gt t.hjk) this
    have hiCap := (Finset.mem_insert.mp hi).resolve_left hiq
    have hjCap := (Finset.mem_insert.mp hj).resolve_left hjq
    exact hcap t hiCap hjCap hkCap

/-- Restrict both sides of a deep-below split to smaller subsets. -/
theorem mono (h : HasDeepBelowSplit χ lower upper)
    {lower' upper' : Finset (Fin n)}
    (hl : lower' ⊆ lower) (hu : upper' ⊆ upper) :
    HasDeepBelowSplit χ lower' upper' := by
  refine ⟨h.disjoint.mono hl hu, ?_⟩
  intro t hi hj hk hnotLower hnotUpper
  have hi' : t.i ∈ lower ∪ upper := by
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (hl hi)
    · exact Finset.mem_union_right _ (hu hi)
  have hj' : t.j ∈ lower ∪ upper := by
    rcases Finset.mem_union.mp hj with hj | hj
    · exact Finset.mem_union_left _ (hl hj)
    · exact Finset.mem_union_right _ (hu hj)
  have hk' : t.k ∈ lower ∪ upper := by
    rcases Finset.mem_union.mp hk with hk | hk
    · exact Finset.mem_union_left _ (hl hk)
    · exact Finset.mem_union_right _ (hu hk)
  have hdisj := Finset.disjoint_left.mp h.disjoint
  have hnotLower' : ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
    rintro ⟨hiL, hjL, hkL⟩
    apply hnotLower
    constructor
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact hi
      · exact (hdisj hiL (hu hi)).elim
    constructor
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact hj
      · exact (hdisj hjL (hu hj)).elim
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact hk
      · exact (hdisj hkL (hu hk)).elim
  have hnotUpper' : ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
    rintro ⟨hiU, hjU, hkU⟩
    apply hnotUpper
    constructor
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact (hdisj (hl hi) hiU).elim
      · exact hi
    constructor
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact (hdisj (hl hj) hjU).elim
      · exact hj
    · rcases Finset.mem_union.mp hk with hk | hk
      · exact (hdisj (hl hk) hkU).elim
      · exact hk
  have hcolor := h.crossing t hi' hj' hk' hnotLower' hnotUpper'
  by_cases hjLower' : t.j ∈ lower'
  · simpa [hjLower', hl hjLower'] using hcolor
  · rw [if_neg hjLower']
    have hjUpper' : t.j ∈ upper' := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (hjLower' hj).elim
      · exact hj
    have hjNotLower : t.j ∉ lower := fun hjLower =>
      hdisj hjLower (hu hjUpper')
    simpa [hjLower', hjNotLower] using hcolor

/-- A cup that meets the lower side of an arbitrary deep-below split can use
at most the two sweep endpoints from the upper side.  Unlike a contiguous
split, both an upper left endpoint and an upper right endpoint are possible. -/
theorem cup_inter_upper_card_le_two
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)}
    (hcupSub : cup ⊆ lower ∪ upper) (hcup : IsCupSet χ cup)
    (hcupLower : (cup ∩ lower).Nonempty) : (cup ∩ upper).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ (cup ∩ upper).card := by omega
  obtain ⟨three, hthreeSub, hthreeCard⟩ :=
    Finset.exists_subset_card_eq hthree
  let e : Fin 3 ↪o Fin n := three.orderEmbOfFin hthreeCard
  let a := e 0
  let b := e 1
  let c := e 2
  have hab : a < b := e.strictMono (by decide)
  have hbc : b < c := e.strictMono (by decide)
  have ha : a ∈ cup ∩ upper := hthreeSub (three.orderEmbOfFin_mem hthreeCard 0)
  have hb : b ∈ cup ∩ upper := hthreeSub (three.orderEmbOfFin_mem hthreeCard 1)
  have hc : c ∈ cup ∩ upper := hthreeSub (three.orderEmbOfFin_mem hthreeCard 2)
  have haCup : a ∈ cup := (Finset.mem_inter.mp ha).1
  have hbCup : b ∈ cup := (Finset.mem_inter.mp hb).1
  have hcCup : c ∈ cup := (Finset.mem_inter.mp hc).1
  have haUpper : a ∈ upper := (Finset.mem_inter.mp ha).2
  have hbUpper : b ∈ upper := (Finset.mem_inter.mp hb).2
  have hcUpper : c ∈ upper := (Finset.mem_inter.mp hc).2
  obtain ⟨p, hp⟩ := hcupLower
  have hpCup : p ∈ cup := (Finset.mem_inter.mp hp).1
  have hpLower : p ∈ lower := (Finset.mem_inter.mp hp).2
  have hdisj := Finset.disjoint_left.mp h.disjoint
  have right_of_middle_upper (t : OrderedTriple n)
      (hti : t.i ∈ cup) (htj : t.j ∈ cup) (htk : t.k ∈ cup)
      (htjUpper : t.j ∈ upper)
      (hsomeLower : t.i ∈ lower ∨ t.j ∈ lower ∨ t.k ∈ lower) :
      χ t = Turn.right := by
    have hiUnion := hcupSub hti
    have hjUnion := hcupSub htj
    have hkUnion := hcupSub htk
    have hjNotLower : t.j ∉ lower := fun hjLower => hdisj hjLower htjUpper
    have hnotLower : ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
      rintro ⟨_, hjLower, _⟩
      exact hjNotLower hjLower
    have hnotUpper : ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
      rintro hallUpper
      rcases hsomeLower with hiLower | hjLower | hkLower
      · exact hdisj hiLower hallUpper.1
      · exact hdisj hjLower hallUpper.2.1
      · exact hdisj hkLower hallUpper.2.2
    simpa [hjNotLower] using
      h.crossing t hiUnion hjUnion hkUnion hnotLower hnotUpper
  have hpa : p ≠ a := fun hpa => hdisj hpLower (hpa ▸ haUpper)
  rcases lt_or_gt_of_ne hpa with hpa | hap
  · let t : OrderedTriple n := ⟨p, a, b, hpa, hab⟩
    have hright : χ t = Turn.right :=
      right_of_middle_upper t hpCup haCup hbCup haUpper (Or.inl hpLower)
    exact Turn.noConfusion (hcup t hpCup haCup hbCup ▸ hright)
  · have hpb : p ≠ b := fun hpb => hdisj hpLower (hpb ▸ hbUpper)
    rcases lt_or_gt_of_ne hpb with hpb | hbp
    · let t : OrderedTriple n := ⟨p, b, c, hpb, hbc⟩
      have hright : χ t = Turn.right :=
        right_of_middle_upper t hpCup hbCup hcCup hbUpper (Or.inl hpLower)
      exact Turn.noConfusion (hcup t hpCup hbCup hcCup ▸ hright)
    · have hpc : p ≠ c := fun hpc => hdisj hpLower (hpc ▸ hcUpper)
      rcases lt_or_gt_of_ne hpc with hpc | hcp
      · let t : OrderedTriple n := ⟨a, b, p, hab, hbp⟩
        have hright : χ t = Turn.right :=
          right_of_middle_upper t haCup hbCup hpCup hbUpper
            (Or.inr (Or.inr hpLower))
        exact Turn.noConfusion (hcup t haCup hbCup hpCup ▸ hright)
      · let t : OrderedTriple n := ⟨b, c, p, hbc, hcp⟩
        have hright : χ t = Turn.right :=
          right_of_middle_upper t hbCup hcCup hpCup hcUpper
            (Or.inr (Or.inr hpLower))
        exact Turn.noConfusion (hcup t hbCup hcCup hpCup ▸ hright)

/-- Pointwise form of the preceding cardinal bound: every upper vertex of a
cup crossing the split is one of the cup's two sweep endpoints. -/
theorem upper_mem_cup_isSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)}
    (hcupSub : cup ⊆ lower ∪ upper) (hcup : IsCupSet χ cup)
    (hcupLower : (cup ∩ lower).Nonempty) {q : Fin n}
    (hqCup : q ∈ cup) (hqUpper : q ∈ upper) : IsSweepEndpoint cup q := by
  by_contra hnot
  rw [IsSweepEndpoint, IsLeftSweepEndpoint, IsRightSweepEndpoint, not_or] at hnot
  push Not at hnot
  obtain ⟨x, hxCup, hxq⟩ := hnot.1
  obtain ⟨y, hyCup, hqy⟩ := hnot.2
  have hxq' : x < q := hxq
  have hqy' : q < y := hqy
  obtain ⟨p, hp⟩ := hcupLower
  have hpCup : p ∈ cup := (Finset.mem_inter.mp hp).1
  have hpLower : p ∈ lower := (Finset.mem_inter.mp hp).2
  have hdisj := Finset.disjoint_left.mp h.disjoint
  have hpq : p ≠ q := fun hpq => hdisj hpLower (hpq ▸ hqUpper)
  have right_of_middle_upper (t : OrderedTriple n)
      (hti : t.i ∈ cup) (htj : t.j ∈ cup) (htk : t.k ∈ cup)
      (htjUpper : t.j ∈ upper)
      (hsomeLower : t.i ∈ lower ∨ t.j ∈ lower ∨ t.k ∈ lower) :
      χ t = Turn.right := by
    have hiUnion := hcupSub hti
    have hjUnion := hcupSub htj
    have hkUnion := hcupSub htk
    have hjNotLower : t.j ∉ lower := fun hjLower => hdisj hjLower htjUpper
    have hnotLower : ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
      rintro ⟨_, hjLower, _⟩
      exact hjNotLower hjLower
    have hnotUpper : ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
      rintro hallUpper
      rcases hsomeLower with hiLower | hjLower | hkLower
      · exact hdisj hiLower hallUpper.1
      · exact hdisj hjLower hallUpper.2.1
      · exact hdisj hkLower hallUpper.2.2
    simpa [hjNotLower] using
      h.crossing t hiUnion hjUnion hkUnion hnotLower hnotUpper
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · let t : OrderedTriple n := ⟨p, q, y, hpq, hqy'⟩
    have hright := right_of_middle_upper t hpCup hqCup hyCup hqUpper
      (Or.inl hpLower)
    exact Turn.noConfusion (hcup t hpCup hqCup hyCup ▸ hright)
  · let t : OrderedTriple n := ⟨x, q, p, hxq', hqp⟩
    have hright := right_of_middle_upper t hxCup hqCup hpCup hqUpper
      (Or.inr (Or.inr hpLower))
    exact Turn.noConfusion (hcup t hxCup hqCup hpCup ▸ hright)

/-- Dually, a cap that meets the upper side of an arbitrary deep-below split
can use at most the two sweep endpoints from the lower side. -/
theorem cap_inter_lower_card_le_two
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)}
    (hcapSub : cap ⊆ lower ∪ upper) (hcap : IsCapSet χ cap)
    (hcapUpper : (cap ∩ upper).Nonempty) : (cap ∩ lower).card ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ (cap ∩ lower).card := by omega
  obtain ⟨three, hthreeSub, hthreeCard⟩ :=
    Finset.exists_subset_card_eq hthree
  let e : Fin 3 ↪o Fin n := three.orderEmbOfFin hthreeCard
  let a := e 0
  let b := e 1
  let c := e 2
  have hab : a < b := e.strictMono (by decide)
  have hbc : b < c := e.strictMono (by decide)
  have ha : a ∈ cap ∩ lower := hthreeSub (three.orderEmbOfFin_mem hthreeCard 0)
  have hb : b ∈ cap ∩ lower := hthreeSub (three.orderEmbOfFin_mem hthreeCard 1)
  have hc : c ∈ cap ∩ lower := hthreeSub (three.orderEmbOfFin_mem hthreeCard 2)
  have haCap : a ∈ cap := (Finset.mem_inter.mp ha).1
  have hbCap : b ∈ cap := (Finset.mem_inter.mp hb).1
  have hcCap : c ∈ cap := (Finset.mem_inter.mp hc).1
  have haLower : a ∈ lower := (Finset.mem_inter.mp ha).2
  have hbLower : b ∈ lower := (Finset.mem_inter.mp hb).2
  have hcLower : c ∈ lower := (Finset.mem_inter.mp hc).2
  obtain ⟨p, hp⟩ := hcapUpper
  have hpCap : p ∈ cap := (Finset.mem_inter.mp hp).1
  have hpUpper : p ∈ upper := (Finset.mem_inter.mp hp).2
  have hdisj := Finset.disjoint_left.mp h.disjoint
  have left_of_middle_lower (t : OrderedTriple n)
      (hti : t.i ∈ cap) (htj : t.j ∈ cap) (htk : t.k ∈ cap)
      (htjLower : t.j ∈ lower)
      (hsomeUpper : t.i ∈ upper ∨ t.j ∈ upper ∨ t.k ∈ upper) :
      χ t = Turn.left := by
    have hiUnion := hcapSub hti
    have hjUnion := hcapSub htj
    have hkUnion := hcapSub htk
    have hjNotUpper : t.j ∉ upper := fun hjUpper => hdisj htjLower hjUpper
    have hnotLower : ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
      rintro hallLower
      rcases hsomeUpper with hiUpper | hjUpper | hkUpper
      · exact hdisj hallLower.1 hiUpper
      · exact hdisj hallLower.2.1 hjUpper
      · exact hdisj hallLower.2.2 hkUpper
    have hnotUpper : ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
      rintro ⟨_, hjUpper, _⟩
      exact hjNotUpper hjUpper
    simpa [htjLower] using
      h.crossing t hiUnion hjUnion hkUnion hnotLower hnotUpper
  have hpa : p ≠ a := fun hpa => hdisj (hpa ▸ haLower) hpUpper
  rcases lt_or_gt_of_ne hpa with hpa | hap
  · let t : OrderedTriple n := ⟨p, a, b, hpa, hab⟩
    have hleft : χ t = Turn.left :=
      left_of_middle_lower t hpCap haCap hbCap haLower (Or.inl hpUpper)
    exact Turn.noConfusion (hcap t hpCap haCap hbCap ▸ hleft)
  · have hpb : p ≠ b := fun hpb => hdisj (hpb ▸ hbLower) hpUpper
    rcases lt_or_gt_of_ne hpb with hpb | hbp
    · let t : OrderedTriple n := ⟨p, b, c, hpb, hbc⟩
      have hleft : χ t = Turn.left :=
        left_of_middle_lower t hpCap hbCap hcCap hbLower (Or.inl hpUpper)
      exact Turn.noConfusion (hcap t hpCap hbCap hcCap ▸ hleft)
    · have hpc : p ≠ c := fun hpc => hdisj (hpc ▸ hcLower) hpUpper
      rcases lt_or_gt_of_ne hpc with hpc | hcp
      · let t : OrderedTriple n := ⟨a, b, p, hab, hbp⟩
        have hleft : χ t = Turn.left :=
          left_of_middle_lower t haCap hbCap hpCap hbLower
            (Or.inr (Or.inr hpUpper))
        exact Turn.noConfusion (hcap t haCap hbCap hpCap ▸ hleft)
      · let t : OrderedTriple n := ⟨b, c, p, hbc, hcp⟩
        have hleft : χ t = Turn.left :=
          left_of_middle_lower t hbCap hcCap hpCap hcLower
            (Or.inr (Or.inr hpUpper))
        exact Turn.noConfusion (hcap t hbCap hcCap hpCap ▸ hleft)

/-- Pointwise dual: every lower vertex of a cap crossing the split is one of
the cap's two sweep endpoints. -/
theorem lower_mem_cap_isSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)}
    (hcapSub : cap ⊆ lower ∪ upper) (hcap : IsCapSet χ cap)
    (hcapUpper : (cap ∩ upper).Nonempty) {q : Fin n}
    (hqCap : q ∈ cap) (hqLower : q ∈ lower) : IsSweepEndpoint cap q := by
  by_contra hnot
  rw [IsSweepEndpoint, IsLeftSweepEndpoint, IsRightSweepEndpoint, not_or] at hnot
  push Not at hnot
  obtain ⟨x, hxCap, hxq⟩ := hnot.1
  obtain ⟨y, hyCap, hqy⟩ := hnot.2
  obtain ⟨p, hp⟩ := hcapUpper
  have hpCap : p ∈ cap := (Finset.mem_inter.mp hp).1
  have hpUpper : p ∈ upper := (Finset.mem_inter.mp hp).2
  have hdisj := Finset.disjoint_left.mp h.disjoint
  have hpq : p ≠ q := fun hpq => hdisj (hpq ▸ hqLower) hpUpper
  have left_of_middle_lower (t : OrderedTriple n)
      (hti : t.i ∈ cap) (htj : t.j ∈ cap) (htk : t.k ∈ cap)
      (htjLower : t.j ∈ lower)
      (hsomeUpper : t.i ∈ upper ∨ t.j ∈ upper ∨ t.k ∈ upper) :
      χ t = Turn.left := by
    have hiUnion := hcapSub hti
    have hjUnion := hcapSub htj
    have hkUnion := hcapSub htk
    have hjNotUpper : t.j ∉ upper := fun hjUpper => hdisj htjLower hjUpper
    have hnotLower : ¬(t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
      rintro hallLower
      rcases hsomeUpper with hiUpper | hjUpper | hkUpper
      · exact hdisj hallLower.1 hiUpper
      · exact hdisj hallLower.2.1 hjUpper
      · exact hdisj hallLower.2.2 hkUpper
    have hnotUpper : ¬(t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
      rintro ⟨_, hjUpper, _⟩
      exact hjNotUpper hjUpper
    simpa [htjLower] using
      h.crossing t hiUnion hjUnion hkUnion hnotLower hnotUpper
  rcases lt_or_gt_of_ne hpq with hpq | hqp
  · let t : OrderedTriple n := ⟨p, q, y, hpq, hqy⟩
    have hleft := left_of_middle_lower t hpCap hqCap hyCap hqLower
      (Or.inl hpUpper)
    exact Turn.noConfusion (hcap t hpCap hqCap hyCap ▸ hleft)
  · let t : OrderedTriple n := ⟨x, q, p, hxq, hqp⟩
    have hleft := left_of_middle_lower t hxCap hqCap hpCap hqLower
      (Or.inr (Or.inr hpUpper))
    exact Turn.noConfusion (hcap t hxCap hqCap hpCap ▸ hleft)

/-- Exact one-vertex cup transition across a deep-below split.  For a
nonempty cup in the lower block, an upper vertex can be adjoined precisely
when it is to the left or right of the whole cup in sweep order. -/
theorem insert_upper_isCupSet_iff_isSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)}
    (hcupSub : cup ⊆ lower) (hcup : IsCupSet χ cup)
    (hcupNonempty : cup.Nonempty) {q : Fin n} (hqUpper : q ∈ upper) :
    IsCupSet χ (insert q cup) ↔ IsSweepEndpoint cup q := by
  constructor
  · intro hinsert
    have hinsertSub : insert q cup ⊆ lower ∪ upper := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxCup
      · exact Finset.mem_union_right _ hqUpper
      · exact Finset.mem_union_left _ (hcupSub hxCup)
    obtain ⟨p, hpCup⟩ := hcupNonempty
    have hinsertLower : ((insert q cup) ∩ lower).Nonempty := by
      exact ⟨p, Finset.mem_inter.mpr
        ⟨Finset.mem_insert_of_mem hpCup, hcupSub hpCup⟩⟩
    have hend := h.upper_mem_cup_isSweepEndpoint hinsertSub hinsert
      hinsertLower (Finset.mem_insert_self q cup) hqUpper
    rcases hend with hend | hend
    · exact Or.inl (fun x hx => hend x (Finset.mem_insert_of_mem hx))
    · exact Or.inr (fun x hx => hend x (Finset.mem_insert_of_mem hx))
  · rintro (hqLeft | hqRight)
    · exact h.insert_upper_isCupSet_of_isLeftSweepEndpoint
        hcupSub hcup hqUpper hqLeft
    · exact h.insert_upper_isCupSet_of_isRightSweepEndpoint
        hcupSub hcup hqUpper hqRight

/-- Exact dual transition: a lower vertex can be adjoined to a nonempty cap
in the upper block precisely at one of its two sweep endpoints. -/
theorem insert_lower_isCapSet_iff_isSweepEndpoint
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)}
    (hcapSub : cap ⊆ upper) (hcap : IsCapSet χ cap)
    (hcapNonempty : cap.Nonempty) {q : Fin n} (hqLower : q ∈ lower) :
    IsCapSet χ (insert q cap) ↔ IsSweepEndpoint cap q := by
  constructor
  · intro hinsert
    have hinsertSub : insert q cap ⊆ lower ∪ upper := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxCap
      · exact Finset.mem_union_left _ hqLower
      · exact Finset.mem_union_right _ (hcapSub hxCap)
    obtain ⟨p, hpCap⟩ := hcapNonempty
    have hinsertUpper : ((insert q cap) ∩ upper).Nonempty := by
      exact ⟨p, Finset.mem_inter.mpr
        ⟨Finset.mem_insert_of_mem hpCap, hcapSub hpCap⟩⟩
    have hend := h.lower_mem_cap_isSweepEndpoint hinsertSub hinsert
      hinsertUpper (Finset.mem_insert_self q cap) hqLower
    rcases hend with hend | hend
    · exact Or.inl (fun x hx => hend x (Finset.mem_insert_of_mem hx))
    · exact Or.inr (fun x hx => hend x (Finset.mem_insert_of_mem hx))
  · rintro (hqLeft | hqRight)
    · exact h.insert_lower_isCapSet_of_isLeftSweepEndpoint
        hcapSub hcap hqLower hqLeft
    · exact h.insert_lower_isCapSet_of_isRightSweepEndpoint
        hcapSub hcap hqLower hqRight

/-- Cardinal recurrence supplied by an upper endpoint: an `r`-cup in the
lower block becomes an `(r+1)`-cup in the union. -/
theorem containsCupSet_succ_of_upper_endpoint
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)} {r : ℕ}
    (hcupSub : cup ⊆ lower) (hcupCard : cup.card = r)
    (hcup : IsCupSet χ cup) {q : Fin n} (hqUpper : q ∈ upper)
    (hqEndpoint : IsSweepEndpoint cup q) :
    ContainsCupSet χ (lower ∪ upper) (r + 1) := by
  have hqNotCup : q ∉ cup := by
    intro hqCup
    exact (Finset.disjoint_left.mp h.disjoint) (hcupSub hqCup) hqUpper
  refine ⟨insert q cup, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxCup
    · exact Finset.mem_union_right _ hqUpper
    · exact Finset.mem_union_left _ (hcupSub hxCup)
  · rw [Finset.card_insert_of_notMem hqNotCup, hcupCard]
  · rcases hqEndpoint with hqLeft | hqRight
    · exact h.insert_upper_isCupSet_of_isLeftSweepEndpoint
        hcupSub hcup hqUpper hqLeft
    · exact h.insert_upper_isCupSet_of_isRightSweepEndpoint
        hcupSub hcup hqUpper hqRight

/-- Dual cardinal recurrence: a lower endpoint extends an `r`-cap in the
upper block to an `(r+1)`-cap in the union. -/
theorem containsCapSet_succ_of_lower_endpoint
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)} {r : ℕ}
    (hcapSub : cap ⊆ upper) (hcapCard : cap.card = r)
    (hcap : IsCapSet χ cap) {q : Fin n} (hqLower : q ∈ lower)
    (hqEndpoint : IsSweepEndpoint cap q) :
    ContainsCapSet χ (lower ∪ upper) (r + 1) := by
  have hqNotCap : q ∉ cap := by
    intro hqCap
    exact (Finset.disjoint_left.mp h.disjoint) hqLower (hcapSub hqCap)
  refine ⟨insert q cap, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxCap
    · exact Finset.mem_union_left _ hqLower
    · exact Finset.mem_union_right _ (hcapSub hxCap)
  · rw [Finset.card_insert_of_notMem hqNotCap, hcapCard]
  · rcases hqEndpoint with hqLeft | hqRight
    · exact h.insert_lower_isCapSet_of_isLeftSweepEndpoint
        hcapSub hcap hqLower hqLeft
    · exact h.insert_lower_isCapSet_of_isRightSweepEndpoint
        hcapSub hcap hqLower hqRight

/-- In a coloring with no `(r+1)`-cup, every upper vertex is strictly
straddled in sweep order by every lower `r`-cup.  This is the negative form of
the endpoint transition and is the constraint needed at saturated boundary
states. -/
theorem cup_straddles_upper_of_not_containsCupSet_succ
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)} {r : ℕ}
    (hcupSub : cup ⊆ lower) (hcupCard : cup.card = r)
    (hcup : IsCupSet χ cup) {q : Fin n} (hqUpper : q ∈ upper)
    (hno : ¬ContainsCupSet χ (lower ∪ upper) (r + 1)) :
    (∃ x ∈ cup, x < q) ∧ ∃ y ∈ cup, q < y := by
  rw [← not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
  intro hqEndpoint
  exact hno (h.containsCupSet_succ_of_upper_endpoint
    hcupSub hcupCard hcup hqUpper hqEndpoint)

/-- Dual saturation constraint: without an `(r+1)`-cap, every lower vertex
is strictly straddled by every upper `r`-cap. -/
theorem cap_straddles_lower_of_not_containsCapSet_succ
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)} {r : ℕ}
    (hcapSub : cap ⊆ upper) (hcapCard : cap.card = r)
    (hcap : IsCapSet χ cap) {q : Fin n} (hqLower : q ∈ lower)
    (hno : ¬ContainsCapSet χ (lower ∪ upper) (r + 1)) :
    (∃ x ∈ cap, x < q) ∧ ∃ y ∈ cap, q < y := by
  rw [← not_isSweepEndpoint_iff_exists_lt_and_exists_gt]
  intro hqEndpoint
  exact hno (h.containsCapSet_succ_of_lower_endpoint
    hcapSub hcapCard hcap hqLower hqEndpoint)

/-- A successful upper extension of a nonempty lower cup has exactly one
directional endpoint state. -/
theorem insert_upper_cup_endpointSide_unique
    (h : HasDeepBelowSplit χ lower upper) {cup : Finset (Fin n)}
    (hcupSub : cup ⊆ lower) (hcup : IsCupSet χ cup)
    (hcupNonempty : cup.Nonempty) {q : Fin n} (hqUpper : q ∈ upper)
    (hinsert : IsCupSet χ (insert q cup)) :
    (IsLeftSweepEndpoint cup q ∨ IsRightSweepEndpoint cup q) ∧
      ¬(IsLeftSweepEndpoint cup q ∧ IsRightSweepEndpoint cup q) := by
  have hendpoint := (h.insert_upper_isCupSet_iff_isSweepEndpoint
    hcupSub hcup hcupNonempty hqUpper).mp hinsert
  have hqNotCup : q ∉ cup := by
    intro hqCup
    exact (Finset.disjoint_left.mp h.disjoint) (hcupSub hqCup) hqUpper
  exact ⟨hendpoint,
    not_isLeft_and_isRightSweepEndpoint hcupNonempty hqNotCup⟩

/-- The dual successful lower extension of an upper cap likewise has a
unique directional endpoint state. -/
theorem insert_lower_cap_endpointSide_unique
    (h : HasDeepBelowSplit χ lower upper) {cap : Finset (Fin n)}
    (hcapSub : cap ⊆ upper) (hcap : IsCapSet χ cap)
    (hcapNonempty : cap.Nonempty) {q : Fin n} (hqLower : q ∈ lower)
    (hinsert : IsCapSet χ (insert q cap)) :
    (IsLeftSweepEndpoint cap q ∨ IsRightSweepEndpoint cap q) ∧
      ¬(IsLeftSweepEndpoint cap q ∧ IsRightSweepEndpoint cap q) := by
  have hendpoint := (h.insert_lower_isCapSet_iff_isSweepEndpoint
    hcapSub hcap hcapNonempty hqLower).mp hinsert
  have hqNotCap : q ∉ cap := by
    intro hqCap
    exact (Finset.disjoint_left.mp h.disjoint) hqLower (hcapSub hqCap)
  exact ⟨hendpoint,
    not_isLeft_and_isRightSweepEndpoint hcapNonempty hqNotCap⟩

/-- If a strong polygon crosses an arbitrary deep-below split, its vertices
on the lower side form a cup. -/
theorem strong_inter_lower_isCupSet
    (h : HasDeepBelowSplit χ lower upper) {polygon : Finset (Fin n)}
    (hpolygonSub : polygon ⊆ lower ∪ upper)
    (hstrong : IsStrongPolygonSet χ polygon)
    (hpolygonUpper : (polygon ∩ upper).Nonempty) :
    IsCupSet χ (polygon ∩ lower) := by
  obtain ⟨p, hp⟩ := hpolygonUpper
  have hpPolygon : p ∈ polygon := (Finset.mem_inter.mp hp).1
  have hpUpper : p ∈ upper := (Finset.mem_inter.mp hp).2
  have hdisj := Finset.disjoint_left.mp h.disjoint
  intro t hi hj hk
  have hiPolygon : t.i ∈ polygon := (Finset.mem_inter.mp hi).1
  have hjPolygon : t.j ∈ polygon := (Finset.mem_inter.mp hj).1
  have hkPolygon : t.k ∈ polygon := (Finset.mem_inter.mp hk).1
  have hiLower : t.i ∈ lower := (Finset.mem_inter.mp hi).2
  have hjLower : t.j ∈ lower := (Finset.mem_inter.mp hj).2
  have hkLower : t.k ∈ lower := (Finset.mem_inter.mp hk).2
  have mixed_left (q : OrderedTriple n)
      (hqi : q.i ∈ polygon) (hqj : q.j ∈ polygon) (hqk : q.k ∈ polygon)
      (hqjLower : q.j ∈ lower)
      (hsomeUpper : q.i ∈ upper ∨ q.j ∈ upper ∨ q.k ∈ upper) :
      χ q = Turn.left := by
    have hiUnion := hpolygonSub hqi
    have hjUnion := hpolygonSub hqj
    have hkUnion := hpolygonSub hqk
    have hjNotUpper : q.j ∉ upper := fun hjUpper => hdisj hqjLower hjUpper
    have hnotLower : ¬(q.i ∈ lower ∧ q.j ∈ lower ∧ q.k ∈ lower) := by
      rintro hallLower
      rcases hsomeUpper with hqiUpper | hqjUpper | hqkUpper
      · exact hdisj hallLower.1 hqiUpper
      · exact hdisj hallLower.2.1 hqjUpper
      · exact hdisj hallLower.2.2 hqkUpper
    have hnotUpper : ¬(q.i ∈ upper ∧ q.j ∈ upper ∧ q.k ∈ upper) := by
      rintro ⟨_, hqjUpper, _⟩
      exact hjNotUpper hqjUpper
    simpa [hqjLower] using
      h.crossing q hiUnion hjUnion hkUnion hnotLower hnotUpper
  have hpi : p ≠ t.i := fun hpi => hdisj (hpi ▸ hiLower) hpUpper
  rcases lt_or_gt_of_ne hpi with hpi | hip
  · have hpj : p < t.j := hpi.trans t.hij
    have hpk : p < t.k := hpj.trans t.hjk
    have heq := (hstrong hpi t.hij t.hjk hpPolygon hiPolygon
      hjPolygon hkPolygon).2
    have hleft := mixed_left ⟨p, t.j, t.k, hpj, t.hjk⟩
      hpPolygon hjPolygon hkPolygon hjLower (Or.inl hpUpper)
    exact heq.symm.trans hleft
  · have hpj : p ≠ t.j := fun hpj => hdisj (hpj ▸ hjLower) hpUpper
    rcases lt_or_gt_of_ne hpj with hpj | hjp
    · have heq := (hstrong hip hpj t.hjk hiPolygon hpPolygon
        hjPolygon hkPolygon).2
      have hleft := mixed_left ⟨p, t.j, t.k, hpj, t.hjk⟩
        hpPolygon hjPolygon hkPolygon hjLower (Or.inl hpUpper)
      exact heq.trans hleft
    · have hpk : p ≠ t.k := fun hpk => hdisj (hpk ▸ hkLower) hpUpper
      rcases lt_or_gt_of_ne hpk with hpk | hkp
      · have heq := (hstrong t.hij hjp hpk hiPolygon hjPolygon
          hpPolygon hkPolygon).1
        have hleft := mixed_left ⟨t.i, t.j, p, t.hij, hjp⟩
          hiPolygon hjPolygon hpPolygon hjLower (Or.inr (Or.inr hpUpper))
        exact heq.symm.trans hleft
      · have heq := (hstrong t.hij t.hjk hkp hiPolygon hjPolygon
          hkPolygon hpPolygon).1
        have hleft := mixed_left ⟨t.i, t.j, p, t.hij, t.hjk.trans hkp⟩
          hiPolygon hjPolygon hpPolygon hjLower (Or.inr (Or.inr hpUpper))
        exact heq.trans hleft

/-- Dually, if a strong polygon crosses an arbitrary deep-below split, its
vertices on the upper side form a cap. -/
theorem strong_inter_upper_isCapSet
    (h : HasDeepBelowSplit χ lower upper) {polygon : Finset (Fin n)}
    (hpolygonSub : polygon ⊆ lower ∪ upper)
    (hstrong : IsStrongPolygonSet χ polygon)
    (hpolygonLower : (polygon ∩ lower).Nonempty) :
    IsCapSet χ (polygon ∩ upper) := by
  obtain ⟨p, hp⟩ := hpolygonLower
  have hpPolygon : p ∈ polygon := (Finset.mem_inter.mp hp).1
  have hpLower : p ∈ lower := (Finset.mem_inter.mp hp).2
  have hdisj := Finset.disjoint_left.mp h.disjoint
  intro t hi hj hk
  have hiPolygon : t.i ∈ polygon := (Finset.mem_inter.mp hi).1
  have hjPolygon : t.j ∈ polygon := (Finset.mem_inter.mp hj).1
  have hkPolygon : t.k ∈ polygon := (Finset.mem_inter.mp hk).1
  have hiUpper : t.i ∈ upper := (Finset.mem_inter.mp hi).2
  have hjUpper : t.j ∈ upper := (Finset.mem_inter.mp hj).2
  have hkUpper : t.k ∈ upper := (Finset.mem_inter.mp hk).2
  have mixed_right (q : OrderedTriple n)
      (hqi : q.i ∈ polygon) (hqj : q.j ∈ polygon) (hqk : q.k ∈ polygon)
      (hqjUpper : q.j ∈ upper)
      (hsomeLower : q.i ∈ lower ∨ q.j ∈ lower ∨ q.k ∈ lower) :
      χ q = Turn.right := by
    have hiUnion := hpolygonSub hqi
    have hjUnion := hpolygonSub hqj
    have hkUnion := hpolygonSub hqk
    have hjNotLower : q.j ∉ lower := fun hjLower => hdisj hjLower hqjUpper
    have hnotLower : ¬(q.i ∈ lower ∧ q.j ∈ lower ∧ q.k ∈ lower) := by
      rintro ⟨_, hqjLower, _⟩
      exact hjNotLower hqjLower
    have hnotUpper : ¬(q.i ∈ upper ∧ q.j ∈ upper ∧ q.k ∈ upper) := by
      rintro hallUpper
      rcases hsomeLower with hqiLower | hqjLower | hqkLower
      · exact hdisj hqiLower hallUpper.1
      · exact hdisj hqjLower hallUpper.2.1
      · exact hdisj hqkLower hallUpper.2.2
    simpa [hjNotLower] using
      h.crossing q hiUnion hjUnion hkUnion hnotLower hnotUpper
  have hpi : p ≠ t.i := fun hpi => hdisj hpLower (hpi ▸ hiUpper)
  rcases lt_or_gt_of_ne hpi with hpi | hip
  · have hpj : p < t.j := hpi.trans t.hij
    have heq := (hstrong hpi t.hij t.hjk hpPolygon hiPolygon
      hjPolygon hkPolygon).2
    have hright := mixed_right ⟨p, t.j, t.k, hpj, t.hjk⟩
      hpPolygon hjPolygon hkPolygon hjUpper (Or.inl hpLower)
    exact heq.symm.trans hright
  · have hpj : p ≠ t.j := fun hpj => hdisj hpLower (hpj ▸ hjUpper)
    rcases lt_or_gt_of_ne hpj with hpj | hjp
    · have heq := (hstrong hip hpj t.hjk hiPolygon hpPolygon
        hjPolygon hkPolygon).2
      have hright := mixed_right ⟨p, t.j, t.k, hpj, t.hjk⟩
        hpPolygon hjPolygon hkPolygon hjUpper (Or.inl hpLower)
      exact heq.trans hright
    · have hpk : p ≠ t.k := fun hpk => hdisj hpLower (hpk ▸ hkUpper)
      rcases lt_or_gt_of_ne hpk with hpk | hkp
      · have heq := (hstrong t.hij hjp hpk hiPolygon hjPolygon
          hpPolygon hkPolygon).1
        have hright := mixed_right ⟨t.i, t.j, p, t.hij, hjp⟩
          hiPolygon hjPolygon hpPolygon hjUpper (Or.inr (Or.inr hpLower))
        exact heq.symm.trans hright
      · have heq := (hstrong t.hij t.hjk hkp hiPolygon hjPolygon
          hkPolygon hpPolygon).1
        have hright := mixed_right ⟨t.i, t.j, p, t.hij, t.hjk.trans hkp⟩
          hiPolygon hjPolygon hpPolygon hjUpper (Or.inr (Or.inr hpLower))
        exact heq.trans hright

/-- A cup in the lower part together with a cap in the upper part is a
strong polygon.  This is the geometric engine of the decomposable-set
argument. -/
theorem cup_union_cap_isStrongPolygonSet
    (h : HasDeepBelowSplit χ lower upper)
    {cup cap : Finset (Fin n)} (hcupSub : cup ⊆ lower)
    (hcapSub : cap ⊆ upper) (hcup : IsCupSet χ cup)
    (hcap : IsCapSet χ cap) :
    IsStrongPolygonSet χ (cup ∪ cap) := by
  intro i j k l hij hjk hkl hi hj hk hl
  have color (t : OrderedTriple n)
      (hti : t.i ∈ cup ∪ cap) (htj : t.j ∈ cup ∪ cap)
      (htk : t.k ∈ cup ∪ cap) :
      χ t = if t.j ∈ cup then Turn.left else Turn.right := by
    by_cases hallCup : t.i ∈ cup ∧ t.j ∈ cup ∧ t.k ∈ cup
    · rw [if_pos hallCup.2.1]
      exact hcup t hallCup.1 hallCup.2.1 hallCup.2.2
    by_cases hallCap : t.i ∈ cap ∧ t.j ∈ cap ∧ t.k ∈ cap
    · rw [if_neg]
      · exact hcap t hallCap.1 hallCap.2.1 hallCap.2.2
      · exact fun hjCup =>
          (Finset.disjoint_left.mp h.disjoint) (hcupSub hjCup)
            (hcapSub hallCap.2.1)
    have hsplit := h.mono hcupSub hcapSub
    exact hsplit.crossing t hti htj htk hallCup hallCap
  constructor
  · rw [color ⟨i, j, k, hij, hjk⟩ hi hj hk,
      color ⟨i, j, l, hij, hjk.trans hkl⟩ hi hj hl]
  · rw [color ⟨i, k, l, hij.trans hjk, hkl⟩ hi hk hl,
      color ⟨j, k, l, hjk, hkl⟩ hj hk hl]

/-- Exact crossing characterization: a set meeting both sides of a deep-below
split is a strong polygon exactly when its lower part is a cup and its upper
part is a cap. -/
theorem isStrongPolygonSet_iff_inter_cup_cap
    (h : HasDeepBelowSplit χ lower upper) {polygon : Finset (Fin n)}
    (hpolygonSub : polygon ⊆ lower ∪ upper)
    (hpolygonLower : (polygon ∩ lower).Nonempty)
    (hpolygonUpper : (polygon ∩ upper).Nonempty) :
    IsStrongPolygonSet χ polygon ↔
      IsCupSet χ (polygon ∩ lower) ∧ IsCapSet χ (polygon ∩ upper) := by
  constructor
  · intro hstrong
    exact ⟨h.strong_inter_lower_isCupSet hpolygonSub hstrong hpolygonUpper,
      h.strong_inter_upper_isCapSet hpolygonSub hstrong hpolygonLower⟩
  · rintro ⟨hcup, hcap⟩
    have hunion : (polygon ∩ lower) ∪ (polygon ∩ upper) = polygon := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_inter.mp hx).1
        · exact (Finset.mem_inter.mp hx).1
      · intro hx
        rcases Finset.mem_union.mp (hpolygonSub hx) with hxLower | hxUpper
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxLower⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxUpper⟩)
    rw [← hunion]
    exact h.cup_union_cap_isStrongPolygonSet
      Finset.inter_subset_right Finset.inter_subset_right hcup hcap

/-- Cardinal form of `cup_union_cap_isStrongPolygonSet`: if the two chains
have total size at least `k`, their union contains a strong `k`-gon. -/
theorem containsStrongPolygonSet_of_cup_cap
    (h : HasDeepBelowSplit χ lower upper)
    {cup cap : Finset (Fin n)} (hcupSub : cup ⊆ lower)
    (hcapSub : cap ⊆ upper) (hcup : IsCupSet χ cup)
    (hcap : IsCapSet χ cap) {k : ℕ}
    (hcard : k ≤ cup.card + cap.card) :
    ContainsStrongPolygonSet χ (lower ∪ upper) k := by
  have hdisjoint : Disjoint cup cap := h.disjoint.mono hcupSub hcapSub
  have hunionCard : (cup ∪ cap).card = cup.card + cap.card :=
    Finset.card_union_of_disjoint hdisjoint
  have hkUnion : k ≤ (cup ∪ cap).card := by simpa [hunionCard] using hcard
  obtain ⟨polygon, hpolygon, hpolygonCard⟩ :=
    Finset.exists_subset_card_eq hkUnion
  refine ⟨polygon, hpolygon.trans ?_, hpolygonCard,
    FinsetPolygon.IsStrongPolygonSet.mono
      (h.cup_union_cap_isStrongPolygonSet hcupSub hcapSub hcup hcap) hpolygon⟩
  exact Finset.union_subset_union hcupSub hcapSub

end HasDeepBelowSplit

/-- Recursive decomposability of a finite set of sweep indices. -/
inductive IsDecomposableOn {n : ℕ} (χ : TripleColoring n) :
    Finset (Fin n) → Prop
  | singleton (i : Fin n) : IsDecomposableOn χ {i}
  | split {lower upper : Finset (Fin n)}
      (hlower : IsDecomposableOn χ lower)
      (hupper : IsDecomposableOn χ upper)
      (hdeep : HasDeepBelowSplit χ lower upper) :
      IsDecomposableOn χ (lower ∪ upper)

/-- A whole sweep coloring is decomposable when its complete index set is. -/
def IsDecomposable {n : ℕ} (χ : TripleColoring n) : Prop :=
  IsDecomposableOn χ Finset.univ

namespace IsDecomposableOn

variable {n : ℕ} {χ : TripleColoring n} {s t : Finset (Fin n)}

theorem nonempty (h : IsDecomposableOn χ s) : s.Nonempty := by
  induction h with
  | singleton i => exact ⟨i, by simp⟩
  | split hlower hupper hdeep ihlower ihupper =>
      exact ihlower.mono (Finset.subset_union_left)

/-- Recursive deep-below colorings satisfy the rank-three signotope law on
every increasing four-set, without assuming sweep realizability. -/
theorem turnSequenceAllowed (h : IsDecomposableOn χ s)
    {i j k l : Fin n} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (hl : l ∈ s) :
    TurnSequenceAllowed
      (χ ⟨i, j, k, hij, hjk⟩)
      (χ ⟨i, j, l, hij, hjk.trans hkl⟩)
      (χ ⟨i, k, l, hij.trans hjk, hkl⟩)
      (χ ⟨j, k, l, hjk, hkl⟩) := by
  induction h generalizing i j k l with
  | singleton x =>
      simp only [Finset.mem_singleton] at hi hj hk hl
      subst i
      subst j
      exact (lt_irrefl x hij).elim
  | @split lower upper hlower hupper hdeep ihlower ihupper =>
      by_cases hallLower :
          i ∈ lower ∧ j ∈ lower ∧ k ∈ lower ∧ l ∈ lower
      · exact ihlower hij hjk hkl hallLower.1 hallLower.2.1
          hallLower.2.2.1 hallLower.2.2.2
      by_cases hallUpper :
          i ∈ upper ∧ j ∈ upper ∧ k ∈ upper ∧ l ∈ upper
      · exact ihupper hij hjk hkl hallUpper.1 hallUpper.2.1
          hallUpper.2.2.1 hallUpper.2.2.2
      exact hdeep.turnSequenceAllowed_of_crossing_four hij hjk hkl
        hi hj hk hl hallLower hallUpper

/-- A decomposable set with at least two vertices exposes a genuine root
split into two nonempty decomposable parts. -/
theorem exists_split (h : IsDecomposableOn χ s) (hcard : 2 ≤ s.card) :
    ∃ lower upper : Finset (Fin n),
      lower.Nonempty ∧ upper.Nonempty ∧
      IsDecomposableOn χ lower ∧ IsDecomposableOn χ upper ∧
      HasDeepBelowSplit χ lower upper ∧ s = lower ∪ upper := by
  cases h with
  | singleton i => simp at hcard
  | @split lower upper hlower hupper hdeep =>
      exact ⟨lower, upper, hlower.nonempty, hupper.nonempty,
        hlower, hupper, hdeep, rfl⟩

/-- Every nonempty subset of a decomposable set is decomposable. -/
theorem subset (h : IsDecomposableOn χ s) (hts : t ⊆ s)
    (ht : t.Nonempty) : IsDecomposableOn χ t := by
  induction h generalizing t with
  | singleton i =>
      obtain ⟨j, hj⟩ := ht
      have hji : j = i := by simpa using hts hj
      subst j
      have htEq : t = {i} := by
        ext x
        constructor
        · intro hx
          simpa using hts hx
        · intro hx
          have hxi : x = i := by simpa using hx
          simpa [hxi] using hj
      subst t
      exact .singleton i
  | @split lower upper hlower hupper hdeep ihlower ihupper =>
      let tlower := t ∩ lower
      let tupper := t ∩ upper
      have htUnion : tlower ∪ tupper = t := by
        apply Finset.Subset.antisymm
        · intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact (Finset.mem_inter.mp hx).1
          · exact (Finset.mem_inter.mp hx).1
        · intro x hx
          have hxparts : x ∈ lower ∪ upper := hts hx
          rcases Finset.mem_union.mp hxparts with hxlower | hxupper
          · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hxlower⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hxupper⟩)
      by_cases htlower : tlower.Nonempty
      · by_cases htupper : tupper.Nonempty
        · rw [← htUnion]
          exact .split
            (ihlower (Finset.inter_subset_right) htlower)
            (ihupper (Finset.inter_subset_right) htupper)
            (hdeep.mono Finset.inter_subset_right Finset.inter_subset_right)
        · have htupperEmpty : tupper = ∅ := Finset.not_nonempty_iff_eq_empty.mp htupper
          have htEq : tlower = t := by simpa [htupperEmpty] using htUnion
          rw [← htEq]
          exact ihlower Finset.inter_subset_right htlower
      · have htlowerEmpty : tlower = ∅ := Finset.not_nonempty_iff_eq_empty.mp htlower
        have htEq : tupper = t := by simpa [htlowerEmpty] using htUnion
        have htupper : tupper.Nonempty := by
          rw [htEq]
          exact ht
        rw [← htEq]
        exact ihupper Finset.inter_subset_right htupper

end IsDecomposableOn

/-- The kernel-checked nine-point signotope certificate applies to the whole
abstract decomposable class: recursive deep-below structure supplies the
one-change hypotheses, so no sweep-realizability assumption is needed. -/
theorem IsDecomposable.containsStrongPolygonSet_five_of_nine_le
    {n : ℕ} {χ : TripleColoring n} (h : IsDecomposable χ) (hn : 9 ≤ n) :
    ContainsStrongPolygonSet χ Finset.univ 5 := by
  let e : Fin 9 ↪o Fin n := Finset.univ.orderEmbOfCardLe (by simpa using hn)
  let ψ : TripleColoring 9 := χ.restrict e
  have hallowed : ∀ (a b c d : Fin 9),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (ψ ⟨a, b, c, hab, hbc⟩)
        (ψ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (ψ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (ψ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    simpa [ψ, TripleColoring.restrict, OrderedTriple.map] using
      h.turnSequenceAllowed (e.strictMono hab) (e.strictMono hbc)
        (e.strictMono hcd) (by simp) (by simp) (by simp) (by simp)
  by_contra hcontains
  have hno : ∀ f : Fin 5 ↪o Fin 9, ¬IsStrongPolygonOn ψ f := by
    intro f hf
    apply hcontains
    let g : Fin 5 ↪o Fin n := f.trans e
    have hg : IsStrongPolygonOn χ g := by
      intro i j k l hij hjk hkl
      simpa [g, ψ, IsStrongPolygonOn, TripleColoring.restrict,
        OrderedTriple.map] using hf hij hjk hkl
    refine ⟨Finset.univ.image g, by simp, ?_,
      FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hg⟩
    exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
  exact (es5CNF_unsat ψ) (es5CNF_of_signotope_noStrong ψ hallowed hno)

/-- The upper half of the exact happy-ending formula, restricted to
decomposable sweep-realizable colorings.  This packages the precise remaining
E3 statement without adding it as an assumption. -/
def DecomposableExactUpperAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}, IsSweepRealizable χ → IsDecomposable χ →
    2 ^ (k - 2) < n → ContainsStrongPolygonSet χ Finset.univ k

/-- E3 is completely discharged at five vertices, and in fact the proof does
not use its sweep-realizability hypothesis. -/
theorem decomposableExactUpperAt_five : DecomposableExactUpperAt 5 := by
  intro n χ _ hdecomposable hcard
  apply hdecomposable.containsStrongPolygonSet_five_of_nine_le
  norm_num at hcard ⊢
  omega

/-- A realizable coloring with more than `2^(k-2)` vertices and no strong
`k`-gon is a combinatorial counterexample to the conjectured upper bound. -/
def IsExactFormulaCounterexample {n : ℕ} (χ : TripleColoring n) (k : ℕ) : Prop :=
  IsSweepRealizable χ ∧ 2 ^ (k - 2) < n ∧
    ¬ContainsStrongPolygonSet χ Finset.univ k

theorem IsExactFormulaCounterexample.not_containsCupSet
    {n k : ℕ} {χ : TripleColoring n} (h : IsExactFormulaCounterexample χ k) :
    ¬ContainsCupSet χ Finset.univ k := by
  intro hcup
  exact h.2.2 (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet hcup)

theorem IsExactFormulaCounterexample.not_containsCapSet
    {n k : ℕ} {χ : TripleColoring n} (h : IsExactFormulaCounterexample χ k) :
    ¬ContainsCapSet χ Finset.univ k := by
  intro hcap
  exact h.2.2 (FinsetPolygon.ContainsCapSet.toContainsStrongPolygonSet hcap)

/-- E4, factored at its exact logical dependency: once E3 is proved at `k`,
every realizable counterexample at `k` is indecomposable. -/
theorem IsExactFormulaCounterexample.not_isDecomposable
    {n k : ℕ} {χ : TripleColoring n} (hE3 : DecomposableExactUpperAt k)
    (h : IsExactFormulaCounterexample χ k) : ¬IsDecomposable χ := by
  intro hdecomp
  exact h.2.2 (hE3 h.1 hdecomp h.2.1)

/-- The lower-bound half is already unconditional: the classical recursive
construction has `2^(k-2)` points and avoids a convex `k`-gon.  Thus proving
`DecomposableExactUpperAt k` is exactly the missing upper half for the
decomposable class. -/
theorem decomposable_exact_lower (k : ℕ) (hk : 3 ≤ k) :
    HasSharpnessExample k (2 ^ (k - 2) + 1) :=
  classical_lower_sharpness k hk

/-- Indices before a sweep cut. -/
def indicesBefore (n cut : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < cut

/-- Indices at or after a sweep cut. -/
def indicesAfter (n cut : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => cut ≤ i.val

@[simp] theorem mem_indicesBefore {n cut : ℕ} {i : Fin n} :
    i ∈ indicesBefore n cut ↔ i.val < cut := by
  simp [indicesBefore]

@[simp] theorem mem_indicesAfter {n cut : ℕ} {i : Fin n} :
    i ∈ indicesAfter n cut ↔ cut ≤ i.val := by
  simp [indicesAfter]

theorem indicesBefore_union_indicesAfter (n cut : ℕ) :
    indicesBefore n cut ∪ indicesAfter n cut = Finset.univ := by
  ext i
  simp [indicesBefore, indicesAfter]
  omega

/-- The earlier contiguous-cut API is a special case of an arbitrary
deep-below partition. -/
theorem HasDeepSplit.toHasDeepBelowSplit {n cut : ℕ}
    {χ : TripleColoring n} (h : HasDeepSplit χ cut) :
    HasDeepBelowSplit χ (indicesBefore n cut) (indicesAfter n cut) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hj
    simp only [mem_indicesBefore] at hi
    simp only [mem_indicesAfter] at hj
    omega
  · intro t hi hj hk hnotBefore hnotAfter
    have hijVal : t.i.val < t.j.val := t.hij
    have hjkVal : t.j.val < t.k.val := t.hjk
    simp only [mem_indicesBefore]
    by_cases hjBefore : t.j.val < cut
    · rw [if_pos hjBefore]
      have hkAfter : cut ≤ t.k.val := by
        by_contra hkNot
        have hkBefore : t.k.val < cut := by omega
        apply hnotBefore
        exact ⟨mem_indicesBefore.mpr (by omega),
          mem_indicesBefore.mpr hjBefore, mem_indicesBefore.mpr hkBefore⟩
      exact h.left_left_right t.hij t.hjk hjBefore hkAfter
    · rw [if_neg hjBefore]
      have hjAfter : cut ≤ t.j.val := by omega
      have hiBefore : t.i.val < cut := by
        by_contra hiNot
        have hiAfter : cut ≤ t.i.val := by omega
        apply hnotAfter
        exact ⟨mem_indicesAfter.mpr hiAfter,
          mem_indicesAfter.mpr hjAfter, mem_indicesAfter.mpr (by omega)⟩
      exact h.left_right_right t.hij t.hjk hiBefore hjAfter

/-- Coordinate-level deep-below relation for two sets of sweep indices.  A
point of the upper set lies above every line through two lower points, and a
lower point lies below every line through two upper points. -/
structure IsGeometricallyDeepBelow {n : ℕ} (P : SweptConfiguration n)
    (lower upper : Finset (Fin n)) : Prop where
  disjoint : Disjoint lower upper
  y_separated : ∀ ⦃i j : Fin n⦄, i ∈ lower → j ∈ upper →
    P.point i 1 < P.point j 1
  upper_above_lower_lines : ∀ ⦃i j k : Fin n⦄, i < j →
    i ∈ lower → j ∈ lower → k ∈ upper →
    0 < orientation (P.point i) (P.point j) (P.point k)
  lower_below_upper_lines : ∀ ⦃i j k : Fin n⦄, i < j →
    i ∈ upper → j ∈ upper → k ∈ lower →
    orientation (P.point i) (P.point j) (P.point k) < 0

/-- The coordinate definition of deep-below induces exactly the crossing
triple law used by recursive decomposability. -/
theorem IsGeometricallyDeepBelow.toHasDeepBelowSplit
    {n : ℕ} {P : SweptConfiguration n}
    {lower upper : Finset (Fin n)}
    (h : IsGeometricallyDeepBelow P lower upper) :
    HasDeepBelowSplit P.tripleColoring lower upper := by
  refine ⟨h.disjoint, ?_⟩
  intro t hi hj hk hnotLower hnotUpper
  have hdisj := Finset.disjoint_left.mp h.disjoint
  have memberCases {x : Fin n} (hx : x ∈ lower ∪ upper) :
      x ∈ lower ∨ x ∈ upper := Finset.mem_union.mp hx
  rcases memberCases hi with hiL | hiU <;>
    rcases memberCases hj with hjL | hjU <;>
      rcases memberCases hk with hkL | hkU
  · exact (hnotLower ⟨hiL, hjL, hkL⟩).elim
  · rw [if_pos hjL]
    exact (P.turn_eq_left_iff t.i t.j t.k).2
      (h.upper_above_lower_lines t.hij hiL hjL hkU)
  · rw [if_neg (fun hjL => hdisj hjL hjU)]
    exact (P.turn_eq_right_iff t.i t.j t.k t.hij t.hjk).2 <| by
      have horient := h.upper_above_lower_lines (t.hij.trans t.hjk) hiL hkL hjU
      rw [orientation_swap_last] at horient
      linarith
  · rw [if_neg (fun hjL => hdisj hjL hjU)]
    exact (P.turn_eq_right_iff t.i t.j t.k t.hij t.hjk).2 <| by
      calc
        orientation (P.point t.i) (P.point t.j) (P.point t.k) =
            orientation (P.point t.j) (P.point t.k) (P.point t.i) :=
          (orientation_cyclic (P.point t.i) (P.point t.j) (P.point t.k)).symm
        _ < 0 := h.lower_below_upper_lines t.hjk hjU hkU hiL
  · rw [if_pos hjL]
    exact (P.turn_eq_left_iff t.i t.j t.k).2 <| by
      calc
        0 < orientation (P.point t.j) (P.point t.k) (P.point t.i) :=
          h.upper_above_lower_lines t.hjk hjL hkL hiU
        _ = orientation (P.point t.i) (P.point t.j) (P.point t.k) :=
          orientation_cyclic (P.point t.i) (P.point t.j) (P.point t.k)
  · rw [if_pos hjL]
    exact (P.turn_eq_left_iff t.i t.j t.k).2 <| by
      have horient := h.lower_below_upper_lines (t.hij.trans t.hjk) hiU hkU hjL
      rw [orientation_swap_last] at horient
      linarith
  · rw [if_neg (fun hjL => hdisj hjL hjU)]
    exact (P.turn_eq_right_iff t.i t.j t.k t.hij t.hjk).2
      (h.lower_below_upper_lines t.hij hiU hjU hkL)
  · exact (hnotUpper ⟨hiU, hjU, hkU⟩).elim

end

end ErdosSzekeres

end
