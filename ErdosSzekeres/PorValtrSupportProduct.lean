module

public import ErdosSzekeres.PorValtrClockwisePeriodization
public import ErdosSzekeres.TothValtrUpper
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# The Pór--Valtr support-product source

This file formalizes the source-side double count in the Pór--Valtr
argument.  A decorated clockwise convex `4 * r`-set is sent to its ordered
even support.  Inside a fiber the odd entries inject into the product of the
corresponding open support cells.  Keeping the support ordered costs a
descending factorial; that factor cancels exactly in the global count.
-/

namespace ErdosSzekeres

noncomputable section

/-- The deliberately coarse denominator used by the source interface. -/
def porValtrSupportDenominator (r : ℕ) : ℕ :=
  2 ^ (32 * r)

/-- The lower bound later extracted from one rich support cell. -/
def porValtrOpenPoolLowerBound (N r : ℕ) : ℕ :=
  (N + porValtrSupportDenominator r - 1) /
      porValtrSupportDenominator r - 1

/-- The cyclic open cell based at support edge `i`.  The exceptional spelling
at zero records the wraparound predecessor explicitly. -/
def porValtrCyclicOpenCell
    (m : ℕ) (anchors : ℕ → Point 2) (i : ℕ) : Set (Point 2) :=
  if i = 0 then
    SukSupportRegion (anchors (m - 1)) (anchors 0)
      (anchors 1) (anchors 2)
  else
    SukSupportRegion (anchors (i - 1)) (anchors i)
      (anchors (i + 1)) (anchors (i + 2))

/-- The exact points of `P` in a cyclic open support cell. -/
noncomputable def porValtrCyclicOpenPool
    (P : Finset (Point 2)) (m : ℕ)
    (anchors : ℕ → Point 2) (i : ℕ) : Finset (Point 2) := by
  classical
  exact P.filter fun p => p ∈ porValtrCyclicOpenCell m anchors i

/-- Ordered cyclic support data together with the source product estimate. -/
structure PorValtrSupportProductData
    (P : Finset (Point 2)) (r : ℕ) where
  anchors : ℕ → Point 2
  sourcePool : ℕ → Finset (Point 2)
  strictCap : SukStrictCapSequence (2 * r) anchors
  periodic : ∀ i, anchors (i + 2 * r) = anchors i
  anchorsSubset : ∀ i, i < 2 * r → anchors i ∈ P
  sourcePool_eq : ∀ i, i < 2 * r →
    sourcePool i = porValtrCyclicOpenPool P (2 * r) anchors i
  sourcePoolsDisjoint : ∀ i, i < 2 * r → ∀ j, j < 2 * r →
    i ≠ j → Disjoint (sourcePool i) (sourcePool j)
  productBound :
    (P.card - 4 * r) ^ (2 * r) ≤
      porValtrSupportDenominator r ^ r *
        ∏ i ∈ Finset.range (2 * r), (sourcePool i).card

private def porValtrConvexSearchSize (r : ℕ) : ℕ :=
  2 ^ (8 * r)

/-- Periodically extend the ordered values of a finite embedding. -/
private def porValtrEmbeddingAnchors
    {P : Finset (Point 2)} {m : ℕ} (hm : 0 < m)
    (z : Fin m ↪ ↥P) (i : ℕ) : Point 2 :=
  (z ⟨i % m, Nat.mod_lt i hm⟩).1

private theorem porValtrEmbeddingAnchors_mod
    {P : Finset (Point 2)} {m : ℕ} (hm : 0 < m)
    (z : Fin m ↪ ↥P) (i : ℕ) :
    porValtrEmbeddingAnchors hm z (i % m) =
      porValtrEmbeddingAnchors hm z i := by
  simp [porValtrEmbeddingAnchors]

private theorem porValtrEmbeddingAnchors_periodic
    {P : Finset (Point 2)} {m : ℕ} (hm : 0 < m)
    (z : Fin m ↪ ↥P) (i : ℕ) :
    porValtrEmbeddingAnchors hm z (i + m) =
      porValtrEmbeddingAnchors hm z i := by
  simp [porValtrEmbeddingAnchors]

private def porValtrEmbeddingRange
    {P : Finset (Point 2)} {m : ℕ} (z : Fin m ↪ ↥P) :
    Finset (Point 2) :=
  Finset.univ.image fun i => (z i).1

private theorem porValtrEmbeddingRange_card
    {P : Finset (Point 2)} {m : ℕ} (z : Fin m ↪ ↥P) :
    (porValtrEmbeddingRange z).card = m := by
  rw [porValtrEmbeddingRange, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    apply z.injective
    exact Subtype.ext hij

private theorem porValtrEmbeddingRange_subset
    {P : Finset (Point 2)} {m : ℕ} (z : Fin m ↪ ↥P) :
    porValtrEmbeddingRange z ⊆ P := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
  exact (z i).property

private def porValtrFullEmbeddingIsStrictCap
    (P : Finset (Point 2)) (r : ℕ)
    (z : Fin (4 * r) ↪ ↥P) : Prop :=
  if hr : 0 < r then
    SukStrictCapSequence (4 * r)
      (porValtrEmbeddingAnchors (by omega) z)
  else False

private def porValtrFullEmbeddings
    (P : Finset (Point 2)) (r : ℕ) :
    Finset (Fin (4 * r) ↪ ↥P) := by
  classical
  exact Finset.univ.filter (porValtrFullEmbeddingIsStrictCap P r)

private theorem mem_porValtrFullEmbeddings
    {P : Finset (Point 2)} {r : ℕ} {z : Fin (4 * r) ↪ ↥P} :
    z ∈ porValtrFullEmbeddings P r ↔
      porValtrFullEmbeddingIsStrictCap P r z := by
  simp [porValtrFullEmbeddings]

private def porValtrEvenEmbedding
    {P : Finset (Point 2)} {r : ℕ}
    (z : Fin (4 * r) ↪ ↥P) : Fin (2 * r) ↪ ↥P where
  toFun i := z ⟨2 * i.1, by omega⟩
  inj' := by
    intro i j hij
    have hidx := z.injective hij
    have hval : 2 * i.1 = 2 * j.1 := by
      simpa using congrArg Fin.val hidx
    apply Fin.ext
    omega

private def porValtrEvenAnchors
    {P : Finset (Point 2)} {r : ℕ} (hr : 0 < r)
    (z : Fin (4 * r) ↪ ↥P) : ℕ → Point 2 :=
  porValtrEmbeddingAnchors (by omega) (porValtrEvenEmbedding z)

private theorem porValtrEvenAnchors_eq_full
    {P : Finset (Point 2)} {r : ℕ} (hr : 0 < r)
    (z : Fin (4 * r) ↪ ↥P) (i : ℕ) :
    porValtrEvenAnchors hr z i =
      porValtrEmbeddingAnchors (by omega : 0 < 4 * r) z (2 * i) := by
  unfold porValtrEvenAnchors porValtrEmbeddingAnchors porValtrEvenEmbedding
  apply congrArg (fun q : ↥P => q.1)
  have hleft : 2 * (i % (2 * r)) < 4 * r := by
    have himod := Nat.mod_lt i (by omega : 0 < 2 * r)
    omega
  have hright : (2 * i) % (4 * r) < 4 * r :=
    Nat.mod_lt _ (by omega)
  change z ⟨2 * (i % (2 * r)), hleft⟩ =
    z ⟨(2 * i) % (4 * r), hright⟩
  apply congrArg z
  apply Fin.ext
  change 2 * (i % (2 * r)) = (2 * i) % (4 * r)
  calc
    2 * (i % (2 * r)) = (2 * i) % (2 * (2 * r)) :=
      (Nat.mul_mod_mul_left 2 i (2 * r)).symm
    _ = (2 * i) % (4 * r) := by
      congr 1; omega

private theorem porValtrEvenAnchors_strictCap
    {P : Finset (Point 2)} {r : ℕ} (hr : 0 < r)
    {z : Fin (4 * r) ↪ ↥P}
    (hz : porValtrFullEmbeddingIsStrictCap P r z) :
    SukStrictCapSequence (2 * r) (porValtrEvenAnchors hr z) := by
  have hz' : SukStrictCapSequence (4 * r)
      (porValtrEmbeddingAnchors (by omega) z) := by
    simpa [porValtrFullEmbeddingIsStrictCap, hr] using hz
  intro i j k hij hjk hk
  rw [porValtrEvenAnchors_eq_full hr z,
    porValtrEvenAnchors_eq_full hr z,
    porValtrEvenAnchors_eq_full hr z]
  exact hz' (by omega) (by omega) (by omega)

/-- All triples in cyclic order have the strict clockwise sign. -/
private def PorValtrCyclicStrictCap
    (m : ℕ) (anchors : ℕ → Point 2) : Prop :=
  ∀ i j k : ℕ, i < m → j < m → k < m →
    ((i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)) →
    orientation (anchors i) (anchors j) (anchors k) < 0

private theorem porValtrEvenAnchors_cyclicStrictCap
    {P : Finset (Point 2)} {r : ℕ} (hr : 0 < r)
    {z : Fin (4 * r) ↪ ↥P}
    (hz : porValtrFullEmbeddingIsStrictCap P r z) :
    PorValtrCyclicStrictCap (2 * r) (porValtrEvenAnchors hr z) := by
  intro i j k hi hj hk hcyc
  rcases hcyc with hijk | hjki | hkij
  · exact porValtrEvenAnchors_strictCap hr hz hijk.1 hijk.2 hk
  · have h := porValtrEvenAnchors_strictCap hr hz hjki.1 hjki.2 hi
    rw [orientation_cyclic
      (porValtrEvenAnchors hr z i)
      (porValtrEvenAnchors hr z j)
      (porValtrEvenAnchors hr z k)] at h
    exact h
  · have h := porValtrEvenAnchors_strictCap hr hz hkij.1 hkij.2 hj
    rw [orientation_cyclic'
      (porValtrEvenAnchors hr z i)
      (porValtrEvenAnchors hr z j)
      (porValtrEvenAnchors hr z k)] at h
    exact h

private theorem porValtrCyclicStrictCap_rotate
    {m s : ℕ} {anchors : ℕ → Point 2}
    (_hm : 0 < m) (hs : s < m)
    (hcyc : PorValtrCyclicStrictCap m anchors) :
    SukStrictCapSequence m (fun i => anchors ((s + i) % m)) := by
  intro a b c hab hbc hc
  have ha : a < m := by omega
  have hb : b < m := by omega
  have hsa : s + a < 2 * m := by omega
  have hsb : s + b < 2 * m := by omega
  have hsc : s + c < 2 * m := by omega
  change orientation (anchors ((s + a) % m))
    (anchors ((s + b) % m)) (anchors ((s + c) % m)) < 0
  by_cases hcm : s + c < m
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hcm]
    exact hcyc (s + a) (s + b) (s + c)
      (by omega) (by omega) hcm (Or.inl ⟨by omega, by omega⟩)
  by_cases hbm : s + b < m
  · have hca : (s + c) % m = s + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hbm, hca]
    exact hcyc (s + a) (s + b) (s + c - m)
      (by omega) hbm (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
  by_cases ham : s + a < m
  · have hba : (s + b) % m = s + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hca : (s + c) % m = s + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt ham, hba, hca]
    exact hcyc (s + a) (s + b - m) (s + c - m)
      ham (by omega) (by omega) (Or.inr (Or.inl ⟨by omega, by omega⟩))
  · have haa : (s + a) % m = s + a - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hba : (s + b) % m = s + b - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hca : (s + c) % m = s + c - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [haa, hba, hca]
    exact hcyc (s + a - m) (s + b - m) (s + c - m)
      (by omega) (by omega) (by omega) (Or.inl ⟨by omega, by omega⟩)

private def porValtrModCell
    (m : ℕ) (anchors : ℕ → Point 2) (i : ℕ) : Set (Point 2) :=
  SukSupportRegion
    (anchors ((i + (m - 1)) % m)) (anchors (i % m))
    (anchors ((i + 1) % m)) (anchors ((i + 2) % m))

private theorem porValtrCyclicOpenCell_eq_modCell
    {P : Finset (Point 2)} {m : ℕ} (hm : 3 ≤ m)
    (z : Fin m ↪ ↥P) (i : ℕ) (hi : i < m) :
    porValtrCyclicOpenCell m (porValtrEmbeddingAnchors (by omega) z) i =
      porValtrModCell m (porValtrEmbeddingAnchors (by omega) z) i := by
  let A := porValtrEmbeddingAnchors (by omega : 0 < m) z
  change porValtrCyclicOpenCell m A i = porValtrModCell m A i
  have hmod (t : ℕ) : A (t % m) = A t :=
    porValtrEmbeddingAnchors_mod (by omega) z t
  by_cases hi0 : i = 0
  · subst i
    simp only [porValtrCyclicOpenCell, if_pos, porValtrModCell,
      Nat.zero_add, Nat.zero_mod]
    rw [Nat.mod_eq_of_lt (by omega : m - 1 < m),
      Nat.mod_eq_of_lt (by omega : 1 < m),
      Nat.mod_eq_of_lt (by omega : 2 < m)]
  · simp only [porValtrCyclicOpenCell, if_neg hi0, porValtrModCell]
    have hprev : (i + (m - 1)) % m = i - 1 := by
      rw [show i + (m - 1) = m + (i - 1) by omega,
        Nat.add_mod, Nat.mod_self, zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega : i - 1 < m)
    rw [hprev]
    rw [hmod i, hmod (i + 1), hmod (i + 2)]

private theorem porValtr_add_mod_offset
    (m s i t : ℕ) :
    (s + ((i + t) % m)) % m = (((s + i) % m) + t) % m := by
  calc
    (s + ((i + t) % m)) % m = (s + (i + t)) % m := by
      simp only [Nat.add_mod, Nat.mod_mod]
    _ = ((s + i) + t) % m := by
      congr 1
      omega
    _ = (((s + i) % m) + t) % m := by
      simp only [Nat.add_mod, Nat.mod_mod]

private theorem porValtrModCell_rotate
    {m s i : ℕ} (_hm : 0 < m) (anchors : ℕ → Point 2) :
    porValtrModCell m (fun k => anchors ((s + k) % m)) i =
    porValtrModCell m anchors ((s + i) % m) := by
  unfold porValtrModCell
  change SukSupportRegion
      (anchors ((s + ((i + (m - 1)) % m)) % m))
      (anchors ((s + (i % m)) % m))
      (anchors ((s + ((i + 1) % m)) % m))
      (anchors ((s + ((i + 2) % m)) % m)) =
    SukSupportRegion
      (anchors ((((s + i) % m) + (m - 1)) % m))
      (anchors (((s + i) % m) % m))
      (anchors ((((s + i) % m) + 1) % m))
      (anchors ((((s + i) % m) + 2) % m))
  have hzero : (s + i % m) % m = (s + i) % m % m := by
    simp only [Nat.add_mod, Nat.mod_mod]
  rw [porValtr_add_mod_offset m s i (m - 1), hzero,
    porValtr_add_mod_offset m s i 1,
    porValtr_add_mod_offset m s i 2]

private theorem porValtrModCells_disjoint_of_forward_gap
    {m s d : ℕ} {anchors : ℕ → Point 2}
    (hm : 6 ≤ m) (hs : s < m)
    (hcyc : PorValtrCyclicStrictCap m anchors)
    (hdlo : 2 ≤ d) (hdhi : d ≤ m - 3) :
    Disjoint (porValtrModCell m anchors s)
      (porValtrModCell m anchors ((s + d) % m)) := by
  let B : ℕ → Point 2 := fun k => anchors ((s + k) % m)
  have hBcap : SukStrictCapSequence m B :=
    porValtrCyclicStrictCap_rotate (by omega) hs hcyc
  have hmpos : 0 < m := lt_of_lt_of_le (by decide) hm
  have hfirst : porValtrModCell m B 0 = porValtrModCell m anchors s := by
    have h := porValtrModCell_rotate hmpos anchors (s := s) (i := 0)
    change porValtrModCell m B 0 =
      porValtrModCell m anchors ((s + 0) % m) at h
    rw [Nat.add_zero, Nat.mod_eq_of_lt hs] at h
    exact h
  have hsecond : porValtrModCell m B d =
      porValtrModCell m anchors ((s + d) % m) := by
    exact porValtrModCell_rotate hmpos anchors (s := s) (i := d)
  rw [← hfirst, ← hsecond]
  rw [Set.disjoint_left]
  intro p hp0 hpd
  simp only [porValtrModCell, SukSupportRegion, Set.mem_setOf_eq,
    Nat.zero_mod, zero_add,
    Nat.mod_eq_of_lt (by omega : m - 1 < m),
    Nat.mod_eq_of_lt (by omega : 1 < m),
    Nat.mod_eq_of_lt (by omega : 2 < m)] at hp0
  have hdlt : d < m := by omega
  have hprev : (d + (m - 1)) % m = d - 1 := by
    rw [show d + (m - 1) = m + (d - 1) by omega,
      Nat.add_mod, Nat.mod_self, zero_add]
    rw [Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega : d - 1 < m)
  simp only [porValtrModCell, hprev, Nat.mod_eq_of_lt hdlt,
    Nat.mod_eq_of_lt (by omega : d + 1 < m),
    Nat.mod_eq_of_lt (by omega : d + 2 < m)] at hpd
  have hwide : p ∈ SukSupportRegion (B 0) (B 1) (B (d + 1)) (B (d + 2)) := by
    apply sukSupportRegion_subset_of_strictCapBlock
      m 0 1 (d + 1) (d + 2) (d - 1) B hBcap
    · omega
    · omega
    · omega
    · omega
    · omega
    · simpa only [show d - 1 + 1 = d by omega,
        show d - 1 + 2 = d + 1 by omega,
        show d - 1 + 3 = d + 2 by omega] using hpd
  exact lt_asymm hp0.1 hwide.2.1

private theorem porValtrModCells_disjoint_of_lt
    {m : ℕ} {anchors : ℕ → Point 2}
    (hm : 6 ≤ m)
    (hcyc : PorValtrCyclicStrictCap m anchors)
    {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i < j) :
    Disjoint (porValtrModCell m anchors i)
      (porValtrModCell m anchors j) := by
  let d := j - i
  have hdpos : 0 < d := by omega
  have hdlt : d < m := by omega
  have htarget : (i + d) % m = j := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  by_cases hd1 : d = 1
  · have hji : j = i + 1 := by omega
    rw [Set.disjoint_left]
    intro p hp hq
    have hi0 : i % m = i := Nat.mod_eq_of_lt hi
    have hi1 : (i + 1) % m = i + 1 := Nat.mod_eq_of_lt (by omega)
    have hprev : (j + (m - 1)) % m = i := by
      rw [show j + (m - 1) = m + i by omega,
        Nat.add_mod, Nat.mod_self, zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt hi
    change 0 < orientation (anchors (i % m))
      (anchors ((i + 1) % m)) p ∧ _ at hp
    rw [hi0, hi1] at hp
    change 0 < orientation (anchors (j % m)) _ p ∧
      orientation (anchors ((j + (m - 1)) % m))
        (anchors (j % m)) p < 0 ∧ _ at hq
    rw [Nat.mod_eq_of_lt hj, hprev, hji] at hq
    exact lt_asymm hp.1 hq.2.1
  by_cases hdlast : d = m - 1
  · have hiZero : i = 0 := by omega
    have hjLast : j = m - 1 := by omega
    subst i
    subst j
    rw [Set.disjoint_left]
    intro p hp hq
    change 0 < orientation (anchors (0 % m)) (anchors (1 % m)) p ∧ _ at hp
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : 1 < m)] at hp
    have hright : (m - 1 + 1) % m = 0 := by
      rw [show m - 1 + 1 = m by omega, Nat.mod_self]
    have hnext : (m - 1 + 2) % m = 1 := by
      rw [show m - 1 + 2 = m + 1 by omega]
      simp only [Nat.add_mod, Nat.mod_self,
        zero_add, Nat.mod_eq_of_lt (by omega : 1 < m)]
    change 0 < orientation _ _ p ∧ _ ∧
      orientation (anchors ((m - 1 + 1) % m))
        (anchors ((m - 1 + 2) % m)) p < 0 at hq
    rw [hright, hnext] at hq
    exact lt_asymm hp.1 hq.2.2
  by_cases hdpenult : d = m - 2
  · have hback : (j + 2) % m = i := by
      rw [show j + 2 = i + m by omega]
      simp only [Nat.add_mod, Nat.mod_self,
        add_zero, Nat.mod_eq_of_lt hi]
    have hdis := porValtrModCells_disjoint_of_forward_gap hm hj hcyc
      (s := j) (d := 2) (by omega) (by omega)
    rw [hback] at hdis
    exact hdis.symm
  · have hdis := porValtrModCells_disjoint_of_forward_gap hm hi hcyc
      (d := d) (by omega) (by omega)
    rw [htarget] at hdis
    exact hdis

private theorem porValtrModCells_disjoint
    {m : ℕ} {anchors : ℕ → Point 2}
    (hm : 6 ≤ m)
    (hcyc : PorValtrCyclicStrictCap m anchors)
    {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    Disjoint (porValtrModCell m anchors i)
      (porValtrModCell m anchors j) := by
  by_cases hijlt : i < j
  · exact porValtrModCells_disjoint_of_lt hm hcyc hi hj hijlt
  · exact (porValtrModCells_disjoint_of_lt hm hcyc hj hi (by omega)).symm

private theorem porValtrSearchThreshold
    (r : ℕ) (hr : 3 ≤ r) :
    Nat.choose (8 * r - 5) (4 * r - 2) + 2 ≤
      porValtrConvexSearchSize r := by
  have hchoose := Nat.choose_le_two_pow (8 * r - 5) (4 * r - 2)
  apply le_trans (Nat.add_le_add_right hchoose 2)
  change 2 ^ (8 * r - 5) + 2 ≤ 2 ^ (8 * r)
  have hexp : 8 * r = (8 * r - 5) + 5 := by omega
  rw [hexp, pow_add]
  have hpow : 1 ≤ 2 ^ (8 * r - 5) := by
    have : 0 < 2 ^ (8 * r - 5) := by positivity
    omega
  norm_num
  omega

private theorem porValtrSearchSize_le_denominator (r : ℕ) :
    porValtrConvexSearchSize r ≤ porValtrSupportDenominator r := by
  unfold porValtrConvexSearchSize porValtrSupportDenominator
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Every search-size subset contains a decorated clockwise `4 * r`-set. -/
private theorem porValtr_exists_fullEmbedding_in_largeSubset
    (P : Finset (Point 2)) (r : ℕ) (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    {X : Finset (Point 2)} (hXP : X ⊆ P)
    (hXcard : X.card = porValtrConvexSearchSize r) :
    ∃ z ∈ porValtrFullEmbeddings P r,
      porValtrEmbeddingRange z ⊆ X := by
  have hgpX : InGeneralPosition X := hgp.mono hXP
  obtain ⟨Y, hYX, hYcard, hYconv⟩ :=
    (tothValtr_upper (4 * r) (by omega)) X
      (by
        rw [hXcard]
        simpa only [show 2 * (4 * r) - 5 = 8 * r - 5 by omega] using
          porValtrSearchThreshold r hr) hgpX
  have hgpY : InGeneralPosition Y := hgpX.mono hYX
  obtain ⟨a, hacap, haperiodic, haY, haimage⟩ :=
    exists_clockwiseStrictCapPeriodization Y (4 * r) (by omega)
      hYcard hYconv hgpY
  have haImageCard :
      ((Finset.range (4 * r)).image a).card = (Finset.range (4 * r)).card := by
    rw [haimage, hYcard, Finset.card_range]
  have haInj : Set.InjOn a (Finset.range (4 * r)) :=
    Finset.injOn_of_card_image_eq haImageCard
  let z : Fin (4 * r) ↪ ↥P := {
    toFun := fun i => ⟨a i.1, hXP (hYX (haY i.1 i.2))⟩
    inj' := by
      intro i j hij
      apply Fin.ext
      apply haInj (Finset.mem_range.mpr i.2) (Finset.mem_range.mpr j.2)
      exact congrArg Subtype.val hij
  }
  refine ⟨z, ?_, ?_⟩
  · rw [mem_porValtrFullEmbeddings]
    rw [porValtrFullEmbeddingIsStrictCap, dif_pos (by omega : 0 < r)]
    intro i j k hij hjk hk
    simpa [porValtrEmbeddingAnchors, z,
      Nat.mod_eq_of_lt (by omega : i < 4 * r),
      Nat.mod_eq_of_lt (by omega : j < 4 * r),
      Nat.mod_eq_of_lt hk] using hacap hij hjk hk
  · intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, _, rfl⟩
    exact hYX (haY i.1 i.2)

private theorem porValtrFullEmbeddings_nonempty
    (P : Finset (Point 2)) (r : ℕ) (hr : 3 ≤ r)
    (hlarge : porValtrSupportDenominator r < P.card)
    (hgp : InGeneralPosition P) :
    (porValtrFullEmbeddings P r).Nonempty := by
  have hMN : porValtrConvexSearchSize r ≤ P.card :=
    (porValtrSearchSize_le_denominator r).trans (Nat.le_of_lt hlarge)
  obtain ⟨X, hXP, hXcard⟩ := Finset.exists_subset_card_eq hMN
  obtain ⟨z, hz, _⟩ :=
    porValtr_exists_fullEmbedding_in_largeSubset P r hr hgp hXP hXcard
  exact ⟨z, hz⟩

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  exact n.lt_two_pow_self.le

private theorem porValtr_four_mul_le_searchSize (r : ℕ) :
    4 * r ≤ porValtrConvexSearchSize r := by
  exact (by omega : 4 * r ≤ 8 * r).trans
    (nat_le_two_pow (8 * r))

private def porValtrLargeSubsets
    (P : Finset (Point 2)) (r : ℕ) : Finset (Finset (Point 2)) :=
  P.powersetCard (porValtrConvexSearchSize r)

private def porValtrLargeContainsFull
    {P : Finset (Point 2)} {r : ℕ}
    (X : Finset (Point 2)) (z : Fin (4 * r) ↪ ↥P) : Prop :=
  porValtrEmbeddingRange z ⊆ X

private noncomputable instance porValtrLargeContainsFull_decidable
    {P : Finset (Point 2)} {r : ℕ} :
    ∀ X z, Decidable
      (@porValtrLargeContainsFull P r X z) :=
  fun _ _ => Classical.dec _

private theorem porValtr_large_fiber_upper
    (P : Finset (Point 2)) (r : ℕ)
    (z : Fin (4 * r) ↪ ↥P) :
    ((porValtrLargeSubsets P r).bipartiteBelow
      porValtrLargeContainsFull z).card ≤
      Nat.choose (P.card - 4 * r)
        (porValtrConvexSearchSize r - 4 * r) := by
  classical
  let R := porValtrEmbeddingRange z
  let source := (porValtrLargeSubsets P r).bipartiteBelow
    porValtrLargeContainsFull z
  let target := (P \ R).powersetCard
    (porValtrConvexSearchSize r - 4 * r)
  have hcard : source.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn (fun X => X \ R)
    · intro X hX
      have hX' : X ∈ porValtrLargeSubsets P r ∧
          porValtrLargeContainsFull X z := by
        simpa [source, Finset.bipartiteBelow] using hX
      have hlarge := Finset.mem_powersetCard.mp hX'.1
      have hRX : R ⊆ X := hX'.2
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro p hp
        have hpX : p ∈ X := Finset.mem_sdiff.mp hp |>.1
        have hpR : p ∉ R := Finset.mem_sdiff.mp hp |>.2
        exact Finset.mem_sdiff.mpr ⟨hlarge.1 hpX, hpR⟩
      · rw [Finset.card_sdiff_of_subset hRX, hlarge.2]
        have hRcard : R.card = 4 * r := by
          simpa [R] using porValtrEmbeddingRange_card z
        rw [hRcard]
    · intro X hX Y hY hdiff
      have hX' : X ∈ porValtrLargeSubsets P r ∧
          porValtrLargeContainsFull X z := by
        simpa [source, Finset.bipartiteBelow] using hX
      have hY' : Y ∈ porValtrLargeSubsets P r ∧
          porValtrLargeContainsFull Y z := by
        simpa [source, Finset.bipartiteBelow] using hY
      have hRX : R ⊆ X := hX'.2
      have hRY : R ⊆ Y := hY'.2
      calc
        X = X \ R ∪ R := (Finset.sdiff_union_of_subset hRX).symm
        _ = Y \ R ∪ R := congrArg (fun T => T ∪ R) hdiff
        _ = Y := Finset.sdiff_union_of_subset hRY
  calc
    _ ≤ target.card := hcard
    _ = Nat.choose (P.card - 4 * r)
        (porValtrConvexSearchSize r - 4 * r) := by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset]
      · rw [porValtrEmbeddingRange_card]
      · exact porValtrEmbeddingRange_subset z

private theorem porValtr_large_fiber_lower
    (P : Finset (Point 2)) (r : ℕ) (hr : 3 ≤ r)
    (hgp : InGeneralPosition P)
    (X : Finset (Point 2)) (hX : X ∈ porValtrLargeSubsets P r) :
    1 ≤ ((porValtrFullEmbeddings P r).bipartiteAbove
      porValtrLargeContainsFull X).card := by
  have hlarge := Finset.mem_powersetCard.mp hX
  obtain ⟨z, hz, hR⟩ :=
    porValtr_exists_fullEmbedding_in_largeSubset P r hr hgp
      hlarge.1 hlarge.2
  exact Finset.card_pos.mpr ⟨z, by
    simp [Finset.bipartiteAbove, hz, porValtrLargeContainsFull]
    exact hR⟩

private theorem porValtr_choose_config_bound
    (P : Finset (Point 2)) (r : ℕ) (hr : 3 ≤ r)
    (hlarge : porValtrSupportDenominator r < P.card)
    (hgp : InGeneralPosition P) :
    Nat.choose P.card (4 * r) ≤
      (porValtrFullEmbeddings P r).card *
        Nat.choose (porValtrConvexSearchSize r) (4 * r) := by
  classical
  have hMN : porValtrConvexSearchSize r ≤ P.card :=
    (porValtrSearchSize_le_denominator r).trans (Nat.le_of_lt hlarge)
  have hKM : 4 * r ≤ porValtrConvexSearchSize r :=
    porValtr_four_mul_le_searchSize r
  have hdouble :
      Nat.choose P.card (porValtrConvexSearchSize r) ≤
        (porValtrFullEmbeddings P r).card *
          Nat.choose (P.card - 4 * r)
            (porValtrConvexSearchSize r - 4 * r) := by
    simpa [porValtrLargeSubsets, Finset.card_powersetCard] using
      (Finset.card_mul_le_card_mul
        (r := porValtrLargeContainsFull)
        (s := porValtrLargeSubsets P r)
        (t := porValtrFullEmbeddings P r)
        (m := 1)
        (n := Nat.choose (P.card - 4 * r)
          (porValtrConvexSearchSize r - 4 * r))
        (porValtr_large_fiber_lower P r hr hgp)
        (fun z _ => porValtr_large_fiber_upper P r z))
  have hmul := Nat.mul_le_mul_right
    (Nat.choose (porValtrConvexSearchSize r) (4 * r)) hdouble
  rw [Nat.choose_mul hKM] at hmul
  have hrespos :
      0 < Nat.choose (P.card - 4 * r)
        (porValtrConvexSearchSize r - 4 * r) := by
    apply Nat.choose_pos
    omega
  apply Nat.le_of_mul_le_mul_right _ hrespos
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul

private theorem porValtr_descFactorial_config_bound
    (P : Finset (Point 2)) (r : ℕ) (hr : 3 ≤ r)
    (hlarge : porValtrSupportDenominator r < P.card)
    (hgp : InGeneralPosition P) :
    P.card.descFactorial (4 * r) ≤
      (porValtrFullEmbeddings P r).card *
        (porValtrConvexSearchSize r).descFactorial (4 * r) := by
  have h := Nat.mul_le_mul_left (Nat.factorial (4 * r))
    (porValtr_choose_config_bound P r hr hlarge hgp)
  simpa only [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

private def porValtrOddPoint
    {P : Finset (Point 2)} {r : ℕ}
    (z : Fin (4 * r) ↪ ↥P) (i : Fin (2 * r)) : Point 2 :=
  (z ⟨2 * i.1 + 1, by omega⟩).1

private theorem porValtrOddPoint_mem
    {P : Finset (Point 2)} {r : ℕ}
    (z : Fin (4 * r) ↪ ↥P) (i : Fin (2 * r)) :
    porValtrOddPoint z i ∈ P :=
  (z ⟨2 * i.1 + 1, by omega⟩).property

private theorem porValtrOddPoint_eq_full
    {P : Finset (Point 2)} {r : ℕ} (hr : 0 < r)
    (z : Fin (4 * r) ↪ ↥P) (i : Fin (2 * r)) :
    porValtrOddPoint z i =
      porValtrEmbeddingAnchors (by omega : 0 < 4 * r) z (2 * i.1 + 1) := by
  simp [porValtrOddPoint, porValtrEmbeddingAnchors,
    Nat.mod_eq_of_lt (by omega : 2 * i.1 + 1 < 4 * r)]

private theorem porValtrOddPoint_mem_modCell
    {P : Finset (Point 2)} {r : ℕ} (hr : 3 ≤ r)
    {z : Fin (4 * r) ↪ ↥P}
    (hz : porValtrFullEmbeddingIsStrictCap P r z)
    (i : Fin (2 * r)) :
    porValtrOddPoint z i ∈
      porValtrModCell (2 * r) (porValtrEvenAnchors (by omega) z) i.1 := by
  have hzcap : SukStrictCapSequence (4 * r)
      (porValtrEmbeddingAnchors (by omega) z) := by
    simpa [porValtrFullEmbeddingIsStrictCap, show 0 < r by omega] using hz
  let F := porValtrEmbeddingAnchors (by omega : 0 < 4 * r) z
  let A := porValtrEvenAnchors (by omega : 0 < r) z
  let p := porValtrOddPoint z i
  have hp : p = F (2 * i.1 + 1) := porValtrOddPoint_eq_full (by omega) z i
  have hA (t : ℕ) : A t = F (2 * t) :=
    porValtrEvenAnchors_eq_full (by omega) z t
  have hi : i.1 < 2 * r := i.2
  change 0 < orientation
      (A (i.1 % (2 * r))) (A ((i.1 + 1) % (2 * r))) p ∧
    orientation (A ((i.1 + (2 * r - 1)) % (2 * r)))
      (A (i.1 % (2 * r))) p < 0 ∧
    orientation (A ((i.1 + 1) % (2 * r)))
      (A ((i.1 + 2) % (2 * r))) p < 0
  rw [hA, hA, hA, hA, hp]
  rw [Nat.mod_eq_of_lt hi]
  by_cases hi0 : i.1 = 0
  · have hprev : (i.1 + (2 * r - 1)) % (2 * r) = 2 * r - 1 := by
      rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have h1 : (i.1 + 1) % (2 * r) = 1 := by
      rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have h2 : (i.1 + 2) % (2 * r) = 2 := by
      rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hprev, h1, h2]
    have hprevEven : 2 * (2 * r - 1) = 4 * r - 2 := by omega
    rw [hi0, hprevEven]
    constructor
    · have hbase := hzcap (i := 0) (j := 1) (k := 2) (by omega) (by omega) (by omega)
      rw [orientation_swap_last] at hbase
      linarith
    constructor
    · have hleft := hzcap (i := 0) (j := 1) (k := 4 * r - 2)
          (by omega) (by omega) (by omega)
      rw [orientation_cyclic
        (F (4 * r - 2)) (F 0) (F 1)] at hleft
      simpa [F] using hleft
    · have hright := hzcap (i := 1) (j := 2) (k := 4)
          (by omega) (by omega) (by omega)
      rw [orientation_cyclic (F 1) (F 2) (F 4)]
      exact hright
  by_cases hilast : i.1 + 1 = 2 * r
  · have hprev : (i.1 + (2 * r - 1)) % (2 * r) = i.1 - 1 := by
      rw [show i.1 + (2 * r - 1) = 2 * r + (i.1 - 1) by omega,
        Nat.add_mod, Nat.mod_self, zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega : i.1 - 1 < 2 * r)
    have h1 : (i.1 + 1) % (2 * r) = 0 := by
      rw [hilast, Nat.mod_self]
    have h2 : (i.1 + 2) % (2 * r) = 1 := by
      rw [show i.1 + 2 = 2 * r + 1 by omega, Nat.add_mod,
        Nat.mod_self, zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hprev, h1, h2]
    have hiEven : 2 * i.1 = 4 * r - 2 := by omega
    have hiOdd : 2 * i.1 + 1 = 4 * r - 1 := by omega
    have hiPrev : 2 * (i.1 - 1) = 4 * r - 4 := by omega
    rw [hiOdd, hiEven, hiPrev]
    simp only [Nat.mul_zero]
    constructor
    · have hbase := hzcap (i := 0) (j := 4 * r - 2) (k := 4 * r - 1)
          (by omega) (by omega) (by omega)
      rw [orientation_swap_last] at hbase
      change -orientation (F 0) (F (4 * r - 1)) (F (4 * r - 2)) < 0 at hbase
      rw [orientation_cyclic'
        (F 0) (F (4 * r - 1)) (F (4 * r - 2))]
      linarith
    constructor
    · exact hzcap (by omega) (by omega) (by omega)
    · exact hzcap (by omega) (by omega) (by omega)
  by_cases hipenult : i.1 + 2 = 2 * r
  · have hprev : (i.1 + (2 * r - 1)) % (2 * r) = i.1 - 1 := by
      rw [show i.1 + (2 * r - 1) = 2 * r + (i.1 - 1) by omega,
        Nat.add_mod, Nat.mod_self, zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega : i.1 - 1 < 2 * r)
    have h1 : (i.1 + 1) % (2 * r) = i.1 + 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (i.1 + 2) % (2 * r) = 0 := by
      rw [hipenult, Nat.mod_self]
    rw [hprev, h1, h2]
    have hiEven : 2 * i.1 = 4 * r - 4 := by omega
    have hiRight : 2 * (i.1 + 1) = 4 * r - 2 := by omega
    have hiOdd : 2 * i.1 + 1 = 4 * r - 3 := by omega
    have hiPrev : 2 * (i.1 - 1) = 4 * r - 6 := by omega
    rw [hiOdd, hiEven, hiRight, hiPrev]
    simp only [Nat.mul_zero]
    constructor
    · have hbase := hzcap (i := 4 * r - 4) (j := 4 * r - 3)
          (k := 4 * r - 2) (by omega) (by omega) (by omega)
      rw [orientation_swap_last] at hbase
      simpa [F] using hbase
    constructor
    · exact hzcap (by omega) (by omega) (by omega)
    · have hright := hzcap (i := 0) (j := 4 * r - 3) (k := 4 * r - 2)
          (by omega) (by omega) (by omega)
      rw [orientation_cyclic'
        (F 0) (F (4 * r - 3)) (F (4 * r - 2))]
      exact hright
  · have hprev : (i.1 + (2 * r - 1)) % (2 * r) = i.1 - 1 := by
      rw [show i.1 + (2 * r - 1) = 2 * r + (i.1 - 1) by omega,
        Nat.add_mod, Nat.mod_self, zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt (by omega : i.1 - 1 < 2 * r)
    have h1 : (i.1 + 1) % (2 * r) = i.1 + 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (i.1 + 2) % (2 * r) = i.1 + 2 := Nat.mod_eq_of_lt (by omega)
    rw [hprev, h1, h2]
    constructor
    · have hbase := hzcap (i := 2 * i.1) (j := 2 * i.1 + 1)
          (k := 2 * i.1 + 2) (by omega) (by omega) (by omega)
      rw [orientation_swap_last] at hbase
      simpa [F] using hbase
    constructor
    · exact hzcap (by omega) (by omega) (by omega)
    · have hright := hzcap (i := 2 * i.1 + 1) (j := 2 * i.1 + 2)
          (k := 2 * i.1 + 4) (by omega) (by omega) (by omega)
      simp only [Nat.mul_add, Nat.mul_one]
      rw [orientation_cyclic
        (F (2 * i.1 + 1)) (F (2 * i.1 + 2)) (F (2 * i.1 + 4))]
      simpa [F] using hright

private theorem porValtrOddPoint_mem_openPool
    {P : Finset (Point 2)} {r : ℕ} (hr : 3 ≤ r)
    {z : Fin (4 * r) ↪ ↥P}
    (hz : porValtrFullEmbeddingIsStrictCap P r z)
    (i : Fin (2 * r)) :
    porValtrOddPoint z i ∈
      porValtrCyclicOpenPool P (2 * r)
        (porValtrEvenAnchors (by omega) z) i.1 := by
  classical
  change porValtrOddPoint z i ∈
    P.filter (fun p => p ∈ porValtrCyclicOpenCell (2 * r)
      (porValtrEvenAnchors (by omega) z) i.1)
  apply Finset.mem_filter.mpr
  constructor
  · exact porValtrOddPoint_mem z i
  · change porValtrOddPoint z i ∈
      porValtrCyclicOpenCell (2 * r)
        (porValtrEmbeddingAnchors (by omega) (porValtrEvenEmbedding z)) i.1
    rw [porValtrCyclicOpenCell_eq_modCell (by omega)
      (porValtrEvenEmbedding z) i.1 i.2]
    exact porValtrOddPoint_mem_modCell hr hz i

private def porValtrEvenFiber
    (P : Finset (Point 2)) (r : ℕ) (e : Fin (2 * r) ↪ ↥P) :
    Finset (Fin (4 * r) ↪ ↥P) :=
  (porValtrFullEmbeddings P r).filter fun z => porValtrEvenEmbedding z = e

private theorem mem_porValtrEvenFiber
    {P : Finset (Point 2)} {r : ℕ} {e : Fin (2 * r) ↪ ↥P}
    {z : Fin (4 * r) ↪ ↥P} :
    z ∈ porValtrEvenFiber P r e ↔
      z ∈ porValtrFullEmbeddings P r ∧ porValtrEvenEmbedding z = e := by
  simp [porValtrEvenFiber]

private theorem porValtr_exists_max_evenFiber
    (P : Finset (Point 2)) (r : ℕ) (hr : 3 ≤ r)
    (hlarge : porValtrSupportDenominator r < P.card)
    (hgp : InGeneralPosition P) :
    ∃ e : Fin (2 * r) ↪ ↥P,
      (porValtrEvenFiber P r e).Nonempty ∧
      (porValtrFullEmbeddings P r).card ≤
        P.card.descFactorial (2 * r) * (porValtrEvenFiber P r e).card := by
  classical
  obtain ⟨z0, hz0⟩ := porValtrFullEmbeddings_nonempty P r hr hlarge hgp
  let e0 := porValtrEvenEmbedding z0
  have hallNonempty :
      (Finset.univ : Finset (Fin (2 * r) ↪ ↥P)).Nonempty := by
    exact ⟨e0, Finset.mem_univ _⟩
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (2 * r) ↪ ↥P))
    (fun e => (porValtrEvenFiber P r e).card) hallNonempty
  have hfiber0 : z0 ∈ porValtrEvenFiber P r e0 := by
    exact mem_porValtrEvenFiber.mpr ⟨hz0, rfl⟩
  have hepos : 0 < (porValtrEvenFiber P r e).card := by
    have h0 : 0 < (porValtrEvenFiber P r e0).card :=
      Finset.card_pos.mpr ⟨z0, hfiber0⟩
    exact h0.trans_le (hmax e0 (Finset.mem_univ _))
  refine ⟨e, Finset.card_pos.mp hepos, ?_⟩
  have hcount :
      (porValtrFullEmbeddings P r).card ≤
        (Finset.univ : Finset (Fin (2 * r) ↪ ↥P)).card *
          (porValtrEvenFiber P r e).card := by
    simpa [porValtrEvenFiber] using
      (Finset.card_mul_le_card_mul
        (r := fun z e => porValtrEvenEmbedding z = e)
        (s := porValtrFullEmbeddings P r)
        (t := (Finset.univ : Finset (Fin (2 * r) ↪ ↥P)))
        (m := 1)
        (n := (porValtrEvenFiber P r e).card)
        (fun z hz => by
          exact Finset.card_pos.mpr ⟨porValtrEvenEmbedding z, by
            simp [Finset.bipartiteAbove]⟩)
        (fun e' _ => by
          simpa [Finset.bipartiteBelow, porValtrEvenFiber] using
            hmax e' (Finset.mem_univ _)))
  simpa [Fintype.card_embedding_eq] using hcount

private theorem porValtr_fullEmbedding_ext
    {P : Finset (Point 2)} {r : ℕ}
    {z w : Fin (4 * r) ↪ ↥P} {e : Fin (2 * r) ↪ ↥P}
    (hz : porValtrEvenEmbedding z = e)
    (hw : porValtrEvenEmbedding w = e)
    (hodd : ∀ i : Fin (2 * r), porValtrOddPoint z i = porValtrOddPoint w i) :
    z = w := by
  apply DFunLike.ext _ _
  intro u
  apply Subtype.ext
  have huDiv : u.1 / 2 < 2 * r := by omega
  let i : Fin (2 * r) := ⟨u.1 / 2, huDiv⟩
  have hdecomp := Nat.mod_add_div u.1 2
  by_cases heven : u.1 % 2 = 0
  · have hu : u.1 = 2 * i.1 := by
      dsimp [i]
      omega
    have hev : (porValtrEvenEmbedding z i).1 =
        (porValtrEvenEmbedding w i).1 := by
      rw [hz, hw]
    have huFin : (⟨2 * i.1, by omega⟩ : Fin (4 * r)) = u :=
      Fin.ext hu.symm
    rw [← huFin]
    exact hev
  · have hmodlt : u.1 % 2 < 2 := Nat.mod_lt _ (by omega)
    have hu : u.1 = 2 * i.1 + 1 := by
      dsimp [i]
      omega
    have ho := hodd i
    have huFin : (⟨2 * i.1 + 1, by omega⟩ : Fin (4 * r)) = u :=
      Fin.ext hu.symm
    rw [← huFin]
    exact ho

private def porValtrPoolsForEven
    (P : Finset (Point 2)) (r : ℕ) (hr : 0 < r)
    (e : Fin (2 * r) ↪ ↥P)
    (i : ℕ) : Finset (Point 2) :=
  porValtrCyclicOpenPool P (2 * r)
    (porValtrEmbeddingAnchors (by omega) e) i

private theorem porValtr_evenFiber_le_poolProduct
    (P : Finset (Point 2)) (r : ℕ) (hr : 3 ≤ r)
    (e : Fin (2 * r) ↪ ↥P) :
    (porValtrEvenFiber P r e).card ≤
      ∏ i ∈ Finset.range (2 * r),
        (porValtrPoolsForEven P r (by omega) e i).card := by
  classical
  let source := ↥(porValtrEvenFiber P r e)
  let target := ∀ i : Fin (2 * r),
    ↥(porValtrPoolsForEven P r (by omega) e i.1)
  let oddVector : source → target := fun z i => ⟨porValtrOddPoint z.1 i, by
    have hzFull : porValtrFullEmbeddingIsStrictCap P r z.1 :=
      mem_porValtrFullEmbeddings.mp (mem_porValtrEvenFiber.mp z.2).1
    have hmem := porValtrOddPoint_mem_openPool hr hzFull i
    have heven := (mem_porValtrEvenFiber.mp z.2).2
    simpa [porValtrPoolsForEven, porValtrEvenAnchors, heven] using hmem⟩
  have hinj : Function.Injective oddVector := by
    intro z w hzw
    apply Subtype.ext
    apply porValtr_fullEmbedding_ext
      (mem_porValtrEvenFiber.mp z.2).2
      (mem_porValtrEvenFiber.mp w.2).2
    intro i
    have ho := congrFun hzw i
    change (⟨porValtrOddPoint z.1 i, _⟩ :
      ↥(porValtrPoolsForEven P r (by omega) e i.1)) =
      ⟨porValtrOddPoint w.1 i, _⟩ at ho
    have hpoints : porValtrOddPoint z.1 i = porValtrOddPoint w.1 i :=
      congrArg (fun q : ↥(porValtrPoolsForEven P r (by omega) e i.1) =>
        (q : Point 2)) ho
    exact hpoints
  have hcard : Fintype.card source ≤ Fintype.card target :=
    Fintype.card_le_of_injective oddVector hinj
  simpa [source, target, Fintype.card_pi, Finset.prod_range] using hcard

/-- A sufficiently large general-position set has an ordered cyclic support
whose exact open pools satisfy the Pór--Valtr product inequality. -/
theorem exists_porValtrSupportProductData
    (P : Finset (Point 2)) (r : ℕ)
    (hr : 3 ≤ r)
    (hlarge : porValtrSupportDenominator r < P.card)
    (hgp : InGeneralPosition P) :
    Nonempty (PorValtrSupportProductData P r) := by
  classical
  obtain ⟨e, heNonempty, hconfigFiber⟩ :=
    porValtr_exists_max_evenFiber P r hr hlarge hgp
  obtain ⟨z, hzFiber⟩ := heNonempty
  have hzFullMem : z ∈ porValtrFullEmbeddings P r :=
    (mem_porValtrEvenFiber.mp hzFiber).1
  have hzFull : porValtrFullEmbeddingIsStrictCap P r z :=
    mem_porValtrFullEmbeddings.mp hzFullMem
  have hzeven : porValtrEvenEmbedding z = e :=
    (mem_porValtrEvenFiber.mp hzFiber).2
  let anchors : ℕ → Point 2 :=
    porValtrEmbeddingAnchors (by omega) e
  let sourcePool : ℕ → Finset (Point 2) := fun i =>
    porValtrPoolsForEven P r (by omega) e i
  have hstrict : SukStrictCapSequence (2 * r) anchors := by
    have h := porValtrEvenAnchors_strictCap (by omega) hzFull
    simpa [anchors, porValtrEvenAnchors, hzeven] using h
  have hcyclic : PorValtrCyclicStrictCap (2 * r) anchors := by
    have h := porValtrEvenAnchors_cyclicStrictCap (by omega) hzFull
    simpa [anchors, porValtrEvenAnchors, hzeven] using h
  have hdisjoint : ∀ i, i < 2 * r → ∀ j, j < 2 * r → i ≠ j →
      Disjoint (sourcePool i) (sourcePool j) := by
    intro i hi j hj hij
    rw [Finset.disjoint_left]
    intro p hpi hpj
    have hpiPool : p ∈ porValtrCyclicOpenPool P (2 * r) anchors i := by
      simpa [sourcePool, porValtrPoolsForEven, anchors] using hpi
    have hpjPool : p ∈ porValtrCyclicOpenPool P (2 * r) anchors j := by
      simpa [sourcePool, porValtrPoolsForEven, anchors] using hpj
    have hpi' : p ∈ porValtrCyclicOpenCell (2 * r) anchors i := by
      have hmem : p ∈ P ∧ p ∈ porValtrCyclicOpenCell (2 * r) anchors i := by
        simpa [porValtrCyclicOpenPool] using hpiPool
      exact hmem.2
    have hpj' : p ∈ porValtrCyclicOpenCell (2 * r) anchors j := by
      have hmem : p ∈ P ∧ p ∈ porValtrCyclicOpenCell (2 * r) anchors j := by
        simpa [porValtrCyclicOpenPool] using hpjPool
      exact hmem.2
    rw [porValtrCyclicOpenCell_eq_modCell (by omega) e i hi] at hpi'
    rw [porValtrCyclicOpenCell_eq_modCell (by omega) e j hj] at hpj'
    exact Set.disjoint_left.mp
      (porValtrModCells_disjoint (by omega) hcyclic hi hj hij) hpi' hpj'
  have hfiberProduct :
      (porValtrEvenFiber P r e).card ≤
        ∏ i ∈ Finset.range (2 * r), (sourcePool i).card := by
    simpa [sourcePool] using porValtr_evenFiber_le_poolProduct P r hr e
  have hglobal := porValtr_descFactorial_config_bound P r hr hlarge hgp
  have hcombined :
      P.card.descFactorial (4 * r) ≤
        (P.card.descFactorial (2 * r) *
          (∏ i ∈ Finset.range (2 * r), (sourcePool i).card)) *
          (porValtrConvexSearchSize r).descFactorial (4 * r) := by
    calc
      P.card.descFactorial (4 * r)
          ≤ (porValtrFullEmbeddings P r).card *
              (porValtrConvexSearchSize r).descFactorial (4 * r) := hglobal
      _ ≤ (P.card.descFactorial (2 * r) *
              (porValtrEvenFiber P r e).card) *
            (porValtrConvexSearchSize r).descFactorial (4 * r) :=
        Nat.mul_le_mul_right _ hconfigFiber
      _ ≤ (P.card.descFactorial (2 * r) *
              (∏ i ∈ Finset.range (2 * r), (sourcePool i).card)) *
            (porValtrConvexSearchSize r).descFactorial (4 * r) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hfiberProduct)
  have hcardLarge : 4 * r ≤ P.card := by
    exact (porValtr_four_mul_le_searchSize r).trans
      ((porValtrSearchSize_le_denominator r).trans (Nat.le_of_lt hlarge))
  have hsupportPos : 0 < P.card.descFactorial (2 * r) :=
    Nat.descFactorial_pos.mpr (by omega)
  have hresidual :
      (P.card - 2 * r).descFactorial (2 * r) ≤
        (∏ i ∈ Finset.range (2 * r), (sourcePool i).card) *
          (porValtrConvexSearchSize r).descFactorial (4 * r) := by
    have hfactor := Nat.descFactorial_mul_descFactorial
      (n := P.card) (k := 2 * r) (m := 4 * r) (by omega)
    apply Nat.le_of_mul_le_mul_left _ hsupportPos
    calc
      P.card.descFactorial (2 * r) *
          (P.card - 2 * r).descFactorial (2 * r) =
          (P.card - 2 * r).descFactorial (2 * r) *
            P.card.descFactorial (2 * r) := Nat.mul_comm _ _
      _ = P.card.descFactorial (4 * r) := by
        simpa only [show 4 * r - 2 * r = 2 * r by omega] using hfactor
      _ ≤ (P.card.descFactorial (2 * r) *
          (∏ i ∈ Finset.range (2 * r), (sourcePool i).card)) *
          (porValtrConvexSearchSize r).descFactorial (4 * r) := hcombined
      _ = P.card.descFactorial (2 * r) *
          ((∏ i ∈ Finset.range (2 * r), (sourcePool i).card) *
            (porValtrConvexSearchSize r).descFactorial (4 * r)) := by
        rw [Nat.mul_assoc]
  have hbaseResidual :
      (P.card - 4 * r) ^ (2 * r) ≤
        (P.card - 2 * r).descFactorial (2 * r) := by
    have hbase : P.card - 4 * r ≤
        P.card - 2 * r + 1 - 2 * r := by omega
    apply le_trans (Nat.pow_le_pow_left hbase (2 * r))
    exact Nat.pow_sub_le_descFactorial (P.card - 2 * r) (2 * r)
  have hsearchScale :
      (porValtrConvexSearchSize r).descFactorial (4 * r) ≤
        porValtrSupportDenominator r ^ r := by
    calc
      (porValtrConvexSearchSize r).descFactorial (4 * r)
          ≤ porValtrConvexSearchSize r ^ (4 * r) :=
        Nat.descFactorial_le_pow _ _
      _ = porValtrSupportDenominator r ^ r := by
        unfold porValtrConvexSearchSize porValtrSupportDenominator
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
  have hproduct :
      (P.card - 4 * r) ^ (2 * r) ≤
        porValtrSupportDenominator r ^ r *
          ∏ i ∈ Finset.range (2 * r), (sourcePool i).card := by
    calc
      (P.card - 4 * r) ^ (2 * r)
          ≤ (P.card - 2 * r).descFactorial (2 * r) := hbaseResidual
      _ ≤ (∏ i ∈ Finset.range (2 * r), (sourcePool i).card) *
          (porValtrConvexSearchSize r).descFactorial (4 * r) := hresidual
      _ ≤ (∏ i ∈ Finset.range (2 * r), (sourcePool i).card) *
          porValtrSupportDenominator r ^ r := Nat.mul_le_mul_left _ hsearchScale
      _ = porValtrSupportDenominator r ^ r *
          ∏ i ∈ Finset.range (2 * r), (sourcePool i).card := Nat.mul_comm _ _
  exact ⟨{
    anchors := anchors
    sourcePool := sourcePool
    strictCap := hstrict
    periodic := fun i => porValtrEmbeddingAnchors_periodic (by omega) e i
    anchorsSubset := fun i hi => by
      simp [anchors, porValtrEmbeddingAnchors, Nat.mod_eq_of_lt hi]
    sourcePool_eq := fun _ _ => rfl
    sourcePoolsDisjoint := hdisjoint
    productBound := hproduct
  }⟩

end

end ErdosSzekeres

end
