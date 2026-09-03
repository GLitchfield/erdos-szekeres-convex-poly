module

public import ErdosSzekeres.DecompositionPrimeNormalization
public import ErdosSzekeres.StructuralChargingTransport

@[expose] public section

/-!
# A predecessor-bicoloring route to the exact doubling recurrence

Instead of normalizing a target-free coloring to a decomposition tree, one may
try to partition its vertices into two classes that both avoid the preceding
strong-polygon size. If such a bicoloring exists uniformly, the exact power of
two follows immediately by induction. This file proves the base case and the
generic recurrence consumer; constructing the bicoloring remains a separate
mathematical obligation.
-/

namespace ErdosSzekeres

/-- Every sweep-realizable coloring avoiding a strong `k`-polygon admits a
partition into two classes, each avoiding a strong `(k-1)`-polygon. -/
def StrongPredecessorBicoloringAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ red blue : Finset (Fin n),
      Disjoint red blue ∧
      red ∪ blue = Finset.univ ∧
      ¬ContainsStrongPolygonSet χ red (k - 1) ∧
      ¬ContainsStrongPolygonSet χ blue (k - 1)

/-- A fractional relaxation of predecessor bicoloring. Positive-weight
subsets avoid the predecessor target, every vertex receives total weight at
least one, and the total rational weight is at most two. -/
def FractionalPredecessorCoverAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ w : Finset (Fin n) → ℚ,
      (∀ support, 0 ≤ w support) ∧
      (∀ support, w support ≠ 0 →
        ¬ContainsStrongPolygonSet χ support (k - 1)) ∧
      (∀ vertex, 1 ≤ ∑ support : Finset (Fin n),
        if vertex ∈ support then w support else 0) ∧
      (∑ support : Finset (Fin n), w support) ≤ 2

/-- A weaker predecessor contract sufficient for exact doubling: every
strong-`k`-free realizable coloring has one strong-`(k-1)`-free support
containing at least half of its vertices. -/
def PredecessorHalfSubsetAt (k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n},
    IsSweepRealizable χ →
    ¬ContainsStrongPolygonSet χ Finset.univ k →
    ∃ support : Finset (Fin n),
      ¬ContainsStrongPolygonSet χ support (k - 1) ∧
      n ≤ 2 * support.card

/-- If every predecessor-sized subset of a set with at least five vertices is
strong, then the whole set is strong.  Every ordered quadruple survives after
erasing some fifth vertex, so the four-index law is inherited from a
predecessor subset. -/
theorem isStrongPolygonSet_of_all_pred_subsets
    {n k : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hk : 5 ≤ k) (hcard : s.card = k)
    (hall : ∀ t : Finset (Fin n), t ⊆ s → t.card = k - 1 →
      IsStrongPolygonSet χ t) :
    IsStrongPolygonSet χ s := by
  intro i j m l hij hjm hml hi hj hm hl
  let quad : Finset (Fin n) := {i, j, m, l}
  have hquadCard : quad.card = 4 := by
    simp [quad, ne_of_lt hij, ne_of_lt (hij.trans hjm),
      ne_of_lt (hij.trans (hjm.trans hml)), ne_of_lt hjm,
      ne_of_lt (hjm.trans hml), ne_of_lt hml]
  have hnotSubset : ¬s ⊆ quad := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hcard, hquadCard] at hle
    omega
  obtain ⟨x, hxs, hxquad⟩ := Finset.not_subset.mp hnotSubset
  have hxi : x ≠ i := by
    intro hxi
    subst x
    exact hxquad (by simp [quad])
  have hxj : x ≠ j := by
    intro hxj
    subst x
    exact hxquad (by simp [quad])
  have hxm : x ≠ m := by
    intro hxm
    subst x
    exact hxquad (by simp [quad])
  have hxl : x ≠ l := by
    intro hxl
    subst x
    exact hxquad (by simp [quad])
  have htCard : (s.erase x).card = k - 1 := by
    rw [Finset.card_erase_of_mem hxs, hcard]
  exact hall (s.erase x) (Finset.erase_subset _ _) htCard hij hjm hml
    (Finset.mem_erase.mpr ⟨hxi.symm, hi⟩)
    (Finset.mem_erase.mpr ⟨hxj.symm, hj⟩)
    (Finset.mem_erase.mpr ⟨hxm.symm, hm⟩)
    (Finset.mem_erase.mpr ⟨hxl.symm, hl⟩)

/-- A non-strong set has an ordered quadruple meeting every vertex deletion
whose remaining facet is strong. -/
theorem exists_ordered_quadruple_hitting_strong_deletions
    {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hnot : ¬ IsStrongPolygonSet χ s) :
    ∃ i j k l : Fin n,
      i < j ∧ j < k ∧ k < l ∧
      i ∈ s ∧ j ∈ s ∧ k ∈ s ∧ l ∈ s ∧
      ∀ d, IsStrongPolygonSet χ (s.erase d) →
        d ∈ ({i, j, k, l} : Finset (Fin n)) := by
  classical
  unfold IsStrongPolygonSet at hnot
  push Not at hnot
  obtain ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl, hbad⟩ := hnot
  refine ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl, ?_⟩
  intro d hstrong
  by_contra hd
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  obtain ⟨hdi, hdj, hdk, hdl⟩ := hd
  have hquad := hstrong hij hjk hkl
    (Finset.mem_erase.mpr ⟨Ne.symm hdi, hi⟩)
    (Finset.mem_erase.mpr ⟨Ne.symm hdj, hj⟩)
    (Finset.mem_erase.mpr ⟨Ne.symm hdk, hk⟩)
    (Finset.mem_erase.mpr ⟨Ne.symm hdl, hl⟩)
  exact hbad hquad.1 hquad.2

/-- At most four vertices of a non-strong set have a strong deletion facet. -/
theorem strong_deletions_card_le_four
    {n : ℕ} {χ : TripleColoring n} {s deletions : Finset (Fin n)}
    (hnot : ¬ IsStrongPolygonSet χ s)
    (hdeletions : ∀ d ∈ deletions, IsStrongPolygonSet χ (s.erase d)) :
    deletions.card ≤ 4 := by
  classical
  obtain ⟨i, j, k, l, hij, hjk, hkl, _hi, _hj, _hk, _hl, hhit⟩ :=
    exists_ordered_quadruple_hitting_strong_deletions hnot
  have hsubset : deletions ⊆ {i, j, k, l} := by
    intro d hd
    exact hhit d (hdeletions d hd)
  calc
    deletions.card ≤ ({i, j, k, l} : Finset (Fin n)).card :=
      Finset.card_le_card hsubset
    _ = 4 := by
      simp [ne_of_lt hij, ne_of_lt (hij.trans hjk),
        ne_of_lt (hij.trans (hjk.trans hkl)), ne_of_lt hjk,
        ne_of_lt (hjk.trans hkl), ne_of_lt hkl]

/-- At most three vertices of a non-strong set of cardinality at least five
have a strong deletion facet.  Four such deletions would be the four vertices
of a bad quadruple; a fifth ambient vertex then repairs both failed
equalities. -/
theorem strong_deletions_card_le_three_of_five_le
    {n : ℕ} {χ : TripleColoring n} {s deletions : Finset (Fin n)}
    (hcard : 5 ≤ s.card) (hnot : ¬ IsStrongPolygonSet χ s)
    (hdeletions : ∀ d ∈ deletions, IsStrongPolygonSet χ (s.erase d)) :
    deletions.card ≤ 3 := by
  classical
  by_contra hlarge
  unfold IsStrongPolygonSet at hnot
  push Not at hnot
  obtain ⟨i, j, k, l, hij, hjk, hkl, hi, hj, hk, hl, hbad⟩ := hnot
  let quad : Finset (Fin n) := {i, j, k, l}
  have hquadCard : quad.card = 4 := by
    simp [quad, ne_of_lt hij, ne_of_lt (hij.trans hjk),
      ne_of_lt (hij.trans (hjk.trans hkl)), ne_of_lt hjk,
      ne_of_lt (hjk.trans hkl), ne_of_lt hkl]
  have hsubset : deletions ⊆ quad := by
    intro d hd
    by_contra hdq
    simp only [quad, Finset.mem_insert, Finset.mem_singleton, not_or] at hdq
    obtain ⟨hdi, hdj, hdk, hdl⟩ := hdq
    have hstrong := hdeletions d hd
    have hgood := hstrong hij hjk hkl
      (Finset.mem_erase.mpr ⟨Ne.symm hdi, hi⟩)
      (Finset.mem_erase.mpr ⟨Ne.symm hdj, hj⟩)
      (Finset.mem_erase.mpr ⟨Ne.symm hdk, hk⟩)
      (Finset.mem_erase.mpr ⟨Ne.symm hdl, hl⟩)
    exact hbad hgood.1 hgood.2
  have hdelCard : deletions.card = 4 := by
    have hle := Finset.card_le_card hsubset
    rw [hquadCard] at hle
    omega
  have hdeq : deletions = quad :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hquadCard, hdelCard])
  have hsi : IsStrongPolygonSet χ (s.erase i) := by
    apply hdeletions i
    rw [hdeq]
    simp [quad]
  have hsj : IsStrongPolygonSet χ (s.erase j) := by
    apply hdeletions j
    rw [hdeq]
    simp [quad]
  have hsk : IsStrongPolygonSet χ (s.erase k) := by
    apply hdeletions k
    rw [hdeq]
    simp [quad]
  have hsl : IsStrongPolygonSet χ (s.erase l) := by
    apply hdeletions l
    rw [hdeq]
    simp [quad]
  have hnotSubset : ¬s ⊆ quad := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hquadCard] at hle
    omega
  obtain ⟨x, hxs, hxquad⟩ := Finset.not_subset.mp hnotSubset
  have hxi : x ≠ i := by
    intro h
    subst x
    exact hxquad (by simp [quad])
  have hxj : x ≠ j := by
    intro h
    subst x
    exact hxquad (by simp [quad])
  have hxk : x ≠ k := by
    intro h
    subst x
    exact hxquad (by simp [quad])
  have hxl : x ≠ l := by
    intro h
    subst x
    exact hxquad (by simp [quad])
  have hxI : x ∈ s.erase i := Finset.mem_erase.mpr ⟨hxi, hxs⟩
  have hjI : j ∈ s.erase i := Finset.mem_erase.mpr ⟨ne_of_gt hij, hj⟩
  have hkI : k ∈ s.erase i :=
    Finset.mem_erase.mpr ⟨ne_of_gt (hij.trans hjk), hk⟩
  have hlI : l ∈ s.erase i :=
    Finset.mem_erase.mpr ⟨ne_of_gt (hij.trans (hjk.trans hkl)), hl⟩
  have hxJ : x ∈ s.erase j := Finset.mem_erase.mpr ⟨hxj, hxs⟩
  have hiJ : i ∈ s.erase j := Finset.mem_erase.mpr ⟨ne_of_lt hij, hi⟩
  have hkJ : k ∈ s.erase j := Finset.mem_erase.mpr ⟨ne_of_gt hjk, hk⟩
  have hlJ : l ∈ s.erase j :=
    Finset.mem_erase.mpr ⟨ne_of_gt (hjk.trans hkl), hl⟩
  have hxK : x ∈ s.erase k := Finset.mem_erase.mpr ⟨hxk, hxs⟩
  have hiK : i ∈ s.erase k :=
    Finset.mem_erase.mpr ⟨ne_of_lt (hij.trans hjk), hi⟩
  have hjK : j ∈ s.erase k := Finset.mem_erase.mpr ⟨ne_of_lt hjk, hj⟩
  have hlK : l ∈ s.erase k := Finset.mem_erase.mpr ⟨ne_of_gt hkl, hl⟩
  have hxL : x ∈ s.erase l := Finset.mem_erase.mpr ⟨hxl, hxs⟩
  have hiL : i ∈ s.erase l :=
    Finset.mem_erase.mpr ⟨ne_of_lt (hij.trans (hjk.trans hkl)), hi⟩
  have hjL : j ∈ s.erase l :=
    Finset.mem_erase.mpr ⟨ne_of_lt (hjk.trans hkl), hj⟩
  have hkL : k ∈ s.erase l := Finset.mem_erase.mpr ⟨ne_of_lt hkl, hk⟩
  have hposition :
      x < i ∨ (i < x ∧ x < j) ∨ (j < x ∧ x < k) ∨
        (k < x ∧ x < l) ∨ l < x := by
    omega
  have hgood :
      χ ⟨i, j, k, hij, hjk⟩ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
        χ ⟨i, k, l, hij.trans hjk, hkl⟩ = χ ⟨j, k, l, hjk, hkl⟩ := by
    rcases hposition with hxiLt | ⟨hix, hxjLt⟩ | ⟨hjx, hxkLt⟩ |
      ⟨hkx, hxlLt⟩ | hlx
    · constructor
      · calc
          χ ⟨i, j, k, hij, hjk⟩ =
              χ ⟨x, j, k, hxiLt.trans hij, hjk⟩ :=
            (hsl hxiLt hij hjk hxL hiL hjL hkL).2.symm
          _ = χ ⟨x, j, l, hxiLt.trans hij, hjk.trans hkl⟩ :=
            (hsi (hxiLt.trans hij) hjk hkl hxI hjI hkI hlI).1
          _ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ :=
            (hsk hxiLt hij (hjk.trans hkl) hxK hiK hjK hlK).2
      · calc
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨x, k, l, hxiLt.trans (hij.trans hjk), hkl⟩ :=
            (hsj hxiLt (hij.trans hjk) hkl hxJ hiJ hkJ hlJ).2.symm
          _ = χ ⟨j, k, l, hjk, hkl⟩ :=
            (hsi (hxiLt.trans hij) hjk hkl hxI hjI hkI hlI).2
    · constructor
      · calc
          χ ⟨i, j, k, hij, hjk⟩ = χ ⟨x, j, k, hxjLt, hjk⟩ :=
            (hsl hix hxjLt hjk hiL hxL hjL hkL).2
          _ = χ ⟨x, j, l, hxjLt, hjk.trans hkl⟩ :=
            (hsi hxjLt hjk hkl hxI hjI hkI hlI).1
          _ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ :=
            (hsk hix hxjLt (hjk.trans hkl) hiK hxK hjK hlK).2.symm
      · calc
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨x, k, l, hxjLt.trans hjk, hkl⟩ :=
            (hsj hix (hxjLt.trans hjk) hkl hiJ hxJ hkJ hlJ).2
          _ = χ ⟨j, k, l, hjk, hkl⟩ :=
            (hsi hxjLt hjk hkl hxI hjI hkI hlI).2
    · constructor
      · calc
          χ ⟨i, j, k, hij, hjk⟩ = χ ⟨i, j, x, hij, hjx⟩ :=
            (hsl hij hjx hxkLt hiL hjL hxL hkL).1.symm
          _ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ :=
            (hsk hij hjx (hxkLt.trans hkl) hiK hjK hxK hlK).1
      · calc
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ = χ ⟨x, k, l, hxkLt, hkl⟩ :=
            (hsj (hij.trans hjx) hxkLt hkl hiJ hxJ hkJ hlJ).2
          _ = χ ⟨j, k, l, hjk, hkl⟩ :=
            (hsi hjx hxkLt hkl hjI hxI hkI hlI).2.symm
    · constructor
      · calc
          χ ⟨i, j, k, hij, hjk⟩ = χ ⟨i, j, x, hij, hjk.trans hkx⟩ :=
            (hsl hij hjk hkx hiL hjL hkL hxL).1
          _ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ :=
            (hsk hij (hjk.trans hkx) hxlLt hiK hjK hxK hlK).1
      · calc
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨i, k, x, hij.trans hjk, hkx⟩ :=
            (hsj (hij.trans hjk) hkx hxlLt hiJ hkJ hxJ hlJ).1.symm
          _ = χ ⟨j, k, x, hjk, hkx⟩ :=
            (hsl hij hjk hkx hiL hjL hkL hxL).2
          _ = χ ⟨j, k, l, hjk, hkl⟩ :=
            (hsi hjk hkx hxlLt hjI hkI hxI hlI).1
    · constructor
      · calc
          χ ⟨i, j, k, hij, hjk⟩ =
              χ ⟨i, j, x, hij, hjk.trans (hkl.trans hlx)⟩ :=
            (hsl hij hjk (hkl.trans hlx) hiL hjL hkL hxL).1
          _ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ :=
            (hsk hij (hjk.trans hkl) hlx hiK hjK hlK hxK).1.symm
      · calc
          χ ⟨i, k, l, hij.trans hjk, hkl⟩ =
              χ ⟨i, k, x, hij.trans hjk, hkl.trans hlx⟩ :=
            (hsj (hij.trans hjk) hkl hlx hiJ hkJ hlJ hxJ).1
          _ = χ ⟨j, k, x, hjk, hkl.trans hlx⟩ :=
            (hsl hij hjk (hkl.trans hlx) hiL hjL hkL hxL).2
          _ = χ ⟨j, k, l, hjk, hkl⟩ :=
            (hsi hjk hkl hlx hjI hkI hlI hxI).1.symm
  exact hbad hgood.1 hgood.2

private def StrongQuadAt {n : ℕ} (χ : TripleColoring n)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d) : Prop :=
  χ ⟨a, b, c, hab, hbc⟩ = χ ⟨a, b, d, hab, hbc.trans hcd⟩ ∧
    χ ⟨a, c, d, hab.trans hbc, hcd⟩ = χ ⟨b, c, d, hbc, hcd⟩

private theorem isStrongPolygonSet_five_of_strongQuads
    {n : ℕ} {χ : TripleColoring n} {a b c d e : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (h1 : StrongQuadAt χ hab hbc hcd)
    (h2 : StrongQuadAt χ hab hbc (hcd.trans hde))
    (h3 : StrongQuadAt χ hab (hbc.trans hcd) hde)
    (h4 : StrongQuadAt χ (hab.trans hbc) hcd hde)
    (h5 : StrongQuadAt χ hbc hcd hde) :
    IsStrongPolygonSet χ {a, b, c, d, e} := by
  classical
  intro i j k l hij hjk hkl hi hj hk hl
  change StrongQuadAt χ hij hjk hkl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem turnSequenceAllowed_second_eq_of_first_eq_third
    {a b c d : Turn} (h : TurnSequenceAllowed a b c d) (hac : a = c) :
    a = b := by
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem turnSequenceAllowed_third_eq_fourth_of_first_ne_third
    {a b c d : Turn} (h : TurnSequenceAllowed a b c d) (hac : a ≠ c) :
    c = d := by
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

/-- On seven ordered labels, four overlapping strong five-sets and the
one-change law force one of the two additional strong five-sets detected by
the seven-local modular discriminator. -/
theorem seven_ordered_strong_fives_force_disjunction
    {n : ℕ} {χ : TripleColoring n} {a b c d e f g : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
    (hef : e < f) (hfg : f < g)
    (hone : OneChangeOn χ {a, b, c, d, e, f, g})
    (hacefg : IsStrongPolygonSet χ {a, c, e, f, g})
    (hadefg : IsStrongPolygonSet χ {a, d, e, f, g})
    (hbcdfg : IsStrongPolygonSet χ {b, c, d, f, g})
    (hbcefg : IsStrongPolygonSet χ {b, c, e, f, g}) :
    IsStrongPolygonSet χ {a, b, e, f, g} ∨
      IsStrongPolygonSet χ {b, d, e, f, g} := by
  classical
  have hac := hab.trans hbc
  have had := hac.trans hcd
  have hae := had.trans hde
  have haf := hae.trans hef
  have hbd := hbc.trans hcd
  have hbe := hbd.trans hde
  have hbf := hbe.trans hef
  have hce := hcd.trans hde
  have hcf := hce.trans hef
  have hdg := hde.trans (hef.trans hfg)
  have heg := hef.trans hfg
  have honeE := hone hab hbd hde (by simp) (by simp) (by simp) (by simp)
  have honeF := hone hab hbd (hde.trans hef) (by simp) (by simp) (by simp) (by simp)
  have honeG := hone hab hbd hdg (by simp) (by simp) (by simp) (by simp)
  have hCef :
      χ ⟨a, d, e, had, hde⟩ = χ ⟨a, d, f, had, hde.trans hef⟩ :=
    (hadefg had hde hef (by simp) (by simp) (by simp) (by simp)).1
  have hCeg : χ ⟨a, d, e, had, hde⟩ = χ ⟨a, d, g, had, hdg⟩ :=
    (hadefg had hde heg (by simp) (by simp) (by simp) (by simp)).1
  by_cases hAC : χ ⟨a, b, d, hab, hbd⟩ = χ ⟨a, d, e, had, hde⟩
  · have hBE : χ ⟨a, b, d, hab, hbd⟩ = χ ⟨a, b, e, hab, hbe⟩ :=
      turnSequenceAllowed_second_eq_of_first_eq_third honeE hAC
    have hBF : χ ⟨a, b, d, hab, hbd⟩ = χ ⟨a, b, f, hab, hbf⟩ :=
      turnSequenceAllowed_second_eq_of_first_eq_third honeF (hAC.trans hCef)
    have hBG :
        χ ⟨a, b, d, hab, hbd⟩ = χ ⟨a, b, g, hab, hbf.trans hfg⟩ :=
      turnSequenceAllowed_second_eq_of_first_eq_third honeG (hAC.trans hCeg)
    have hACEF := hacefg hac hce hef (by simp) (by simp) (by simp) (by simp)
    have hBCEF := hbcefg hbc hce hef (by simp) (by simp) (by simp) (by simp)
    have hACEG := hacefg hac hce heg (by simp) (by simp) (by simp) (by simp)
    have hBCEG := hbcefg hbc hce heg (by simp) (by simp) (by simp) (by simp)
    have hACFG := hacefg hac hcf hfg (by simp) (by simp) (by simp) (by simp)
    have hBCFG := hbcefg hbc hcf hfg (by simp) (by simp) (by simp) (by simp)
    have h1 : StrongQuadAt χ hab hbe hef :=
      ⟨hBE.symm.trans hBF, hACEF.2.trans hBCEF.2.symm⟩
    have h2 : StrongQuadAt χ hab hbe heg :=
      ⟨hBE.symm.trans hBG, hACEG.2.trans hBCEG.2.symm⟩
    have h3 : StrongQuadAt χ hab hbf hfg :=
      ⟨hBF.symm.trans hBG, hACFG.2.trans hBCFG.2.symm⟩
    have h4 : StrongQuadAt χ hae hef hfg :=
      hacefg hae hef hfg (by simp) (by simp) (by simp) (by simp)
    have h5 : StrongQuadAt χ hbe hef hfg :=
      hbcefg hbe hef hfg (by simp) (by simp) (by simp) (by simp)
    exact Or.inl (isStrongPolygonSet_five_of_strongQuads hab hbe hef hfg h1 h2 h3 h4 h5)
  · have hDE : χ ⟨a, d, e, had, hde⟩ = χ ⟨b, d, e, hbd, hde⟩ :=
      turnSequenceAllowed_third_eq_fourth_of_first_ne_third honeE hAC
    have hACF : χ ⟨a, b, d, hab, hbd⟩ ≠ χ ⟨a, d, f, had, hde.trans hef⟩ := by
      intro h
      exact hAC (h.trans hCef.symm)
    have hACG : χ ⟨a, b, d, hab, hbd⟩ ≠ χ ⟨a, d, g, had, hdg⟩ := by
      intro h
      exact hAC (h.trans hCeg.symm)
    have hDF :
        χ ⟨a, d, f, had, hde.trans hef⟩ = χ ⟨b, d, f, hbd, hde.trans hef⟩ :=
      turnSequenceAllowed_third_eq_fourth_of_first_ne_third honeF hACF
    have hDG : χ ⟨a, d, g, had, hdg⟩ = χ ⟨b, d, g, hbd, hdg⟩ :=
      turnSequenceAllowed_third_eq_fourth_of_first_ne_third honeG hACG
    have hACEF := hacefg hac hce hef (by simp) (by simp) (by simp) (by simp)
    have hBCEF := hbcefg hbc hce hef (by simp) (by simp) (by simp) (by simp)
    have hADEF := hadefg had hde hef (by simp) (by simp) (by simp) (by simp)
    have hACEG := hacefg hac hce heg (by simp) (by simp) (by simp) (by simp)
    have hBCEG := hbcefg hbc hce heg (by simp) (by simp) (by simp) (by simp)
    have hADEG := hadefg had hde heg (by simp) (by simp) (by simp) (by simp)
    have hACFG := hacefg hac hcf hfg (by simp) (by simp) (by simp) (by simp)
    have hBCFG := hbcdfg hbc hcf hfg (by simp) (by simp) (by simp) (by simp)
    have hADFG :=
      hadefg had (hde.trans hef) hfg (by simp) (by simp) (by simp) (by simp)
    have h1 : StrongQuadAt χ hbd hde hef :=
      ⟨hDE.symm.trans (hCef.trans hDF),
        hBCEF.2.trans (hACEF.2.symm.trans hADEF.2)⟩
    have h2 : StrongQuadAt χ hbd hde heg :=
      ⟨hDE.symm.trans (hCeg.trans hDG),
        hBCEG.2.trans (hACEG.2.symm.trans hADEG.2)⟩
    have h3 : StrongQuadAt χ hbd (hde.trans hef) hfg :=
      ⟨hDF.symm.trans (hCef.symm.trans (hCeg.trans hDG)),
        hBCFG.2.trans (hACFG.2.symm.trans hADFG.2)⟩
    have h4 : StrongQuadAt χ hbe hef hfg :=
      hbcefg hbe hef hfg (by simp) (by simp) (by simp) (by simp)
    have h5 : StrongQuadAt χ hde hef hfg :=
      hadefg hde hef hfg (by simp) (by simp) (by simp) (by simp)
    exact Or.inr (isStrongPolygonSet_five_of_strongQuads hbd hde hef hfg h1 h2 h3 h4 h5)

/-- On at most `2 * k - 3` vertices, strong-`k` avoidance already forces a
predecessor bicoloring.  Below the boundary the two classes can both be made
too small to contain `k-1` vertices.  At equality, failure of every
predecessor set would make every `k`-set strong by the local four-index law. -/
theorem exists_strongPredecessorBicoloring_of_card_le_two_mul_sub_three
    {k : ℕ} (hk : 5 ≤ k) :
    ∀ {n : ℕ} {χ : TripleColoring n},
      n ≤ 2 * k - 3 →
      ¬ContainsStrongPolygonSet χ Finset.univ k →
      ∃ red blue : Finset (Fin n),
        Disjoint red blue ∧
        red ∪ blue = Finset.univ ∧
        ¬ContainsStrongPolygonSet χ red (k - 1) ∧
        ¬ContainsStrongPolygonSet χ blue (k - 1) := by
  intro n χ hn hnoStrong
  have small_is_free (support : Finset (Fin n))
      (hsmall : support.card < k - 1) :
      ¬ContainsStrongPolygonSet χ support (k - 1) := by
    rintro ⟨polygon, hsub, hcard, _⟩
    have hle := Finset.card_le_card hsub
    omega
  by_cases hlow : n ≤ 2 * (k - 2)
  · by_cases hnSmall : n ≤ k - 2
    · refine ⟨Finset.univ, ∅, Finset.disjoint_empty_right _,
        by simp, ?_, small_is_free ∅ (by simp; omega)⟩
      apply small_is_free
      simp
      omega
    · have hredExists : ∃ red : Finset (Fin n),
          red ⊆ Finset.univ ∧ red.card = k - 2 := by
        apply Finset.exists_subset_card_eq
        simp
        omega
      obtain ⟨red, hredSub, hredCard⟩ := hredExists
      let blue := Finset.univ \ red
      have hblueCard : blue.card ≤ k - 2 := by
        dsimp [blue]
        rw [Finset.card_sdiff_of_subset hredSub]
        simp
        omega
      refine ⟨red, blue, Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hredSub, ?_, ?_⟩
      · apply small_is_free
        rw [hredCard]
        omega
      · apply small_is_free
        omega
  · have hnEq : n = 2 * k - 3 := by omega
    have hfreePred : ∃ red : Finset (Fin n),
        red ⊆ Finset.univ ∧ red.card = k - 1 ∧
        ¬IsStrongPolygonSet χ red := by
      by_contra hnone
      push Not at hnone
      have hkLeN : k ≤ n := by omega
      obtain ⟨polygon, hpolygonSub, hpolygonCard⟩ :=
        Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset (Fin n))) (by simpa using hkLeN)
      have hpolygonStrong : IsStrongPolygonSet χ polygon := by
        apply isStrongPolygonSet_of_all_pred_subsets hk hpolygonCard
        intro t htSub htCard
        exact hnone t (htSub.trans hpolygonSub) htCard
      exact hnoStrong ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩
    obtain ⟨red, hredSub, hredCard, hredFree⟩ := hfreePred
    let blue := Finset.univ \ red
    have hblueCard : blue.card = k - 2 := by
      dsimp [blue]
      rw [Finset.card_sdiff_of_subset hredSub]
      simp [hnEq, hredCard]
      omega
    refine ⟨red, blue, Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hredSub, ?_, ?_⟩
    · rintro ⟨polygon, hpolygonSub, hpolygonCard, hpolygonStrong⟩
      have hpolygonEq : polygon = red :=
        Finset.eq_of_subset_of_card_le hpolygonSub (by omega)
      subst polygon
      exact hredFree hpolygonStrong
    · apply small_is_free
      rw [hblueCard]
      omega

/-- Three vertices always form a strong polygon, so the exact sweep upper
bound starts at `k = 3`. -/
theorem sweepExactUpperAt_three : SweepExactUpperAt 3 := by
  intro n χ _ hcard
  have hn : 3 ≤ n := by norm_num at hcard ⊢; omega
  let f : Fin 3 ↪o Fin n := Fin.castLEOrderEmb hn
  have hstrong : IsStrongPolygonOn χ f := by
    intro i j k l hij hjk hkl
    omega
  refine ⟨Finset.univ.image f, Finset.subset_univ _, ?_,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hstrong⟩
  simpa using Finset.card_image_of_injective Finset.univ f.injective

/-- A predecessor bicoloring converts the exact upper bound at `k-1` into the
exact upper bound at `k`. Each color class has at most `2^(k-3)` vertices, so
their disjoint union has at most `2^(k-2)` vertices. -/
theorem sweepExactUpperAt_of_predecessorBicoloring
    {k : ℕ} (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hbicolor : StrongPredecessorBicoloringAt k) :
    SweepExactUpperAt k := by
  intro n χ hreal hcard
  by_contra hno
  obtain ⟨red, blue, hdisjoint, hunion, hred, hblue⟩ :=
    hbicolor hreal hno
  have hredCard : red.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < red.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin red.card ↪o Fin n := red.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact hred hmapped
  have hblueCard : blue.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < blue.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin blue.card ↪o Fin n := blue.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact hblue hmapped
  have hn : n = red.card + blue.card := by
    have hunionCard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisjoint] at hunionCard
    simpa using hunionCard.symm
  have hkpow : k - 2 = (k - 3) + 1 := by omega
  rw [hkpow, pow_succ] at hcard
  omega

/-- One predecessor-free support containing at least half of the vertices
gives the same exact doubling recurrence as a full predecessor bicoloring. -/
theorem sweepExactUpperAt_of_predecessorHalfSubset
    {k : ℕ} (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hhalf : PredecessorHalfSubsetAt k) :
    SweepExactUpperAt k := by
  intro n χ hreal hcard
  by_contra hno
  obtain ⟨support, hfree, hhalfCard⟩ := hhalf hreal hno
  have hsupportCard : support.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < support.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin support.card ↪o Fin n := support.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact hfree hmapped
  have hkpow : k - 2 = (k - 3) + 1 := by omega
  rw [hkpow, pow_succ] at hcard
  omega

/-- Integral predecessor bicoloring implies the weaker half-subset
contract by selecting the larger color class. -/
theorem predecessorHalfSubsetAt_of_bicoloring
    {k : ℕ} (hbicolor : StrongPredecessorBicoloringAt k) :
    PredecessorHalfSubsetAt k := by
  intro n χ hreal hno
  obtain ⟨red, blue, hdisjoint, hunion, hred, hblue⟩ :=
    hbicolor hreal hno
  have hn : n = red.card + blue.card := by
    have hunionCard := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisjoint] at hunionCard
    simpa using hunionCard.symm
  by_cases hle : blue.card ≤ red.card
  · exact ⟨red, hred, by omega⟩
  · exact ⟨blue, hblue, by omega⟩

/-- Integral predecessor bicoloring implies the fractional relaxation by
putting weight one on each color class.  If both classes are empty, their
coincident support simply receives weight two. -/
theorem fractionalPredecessorCoverAt_of_bicoloring
    {k : ℕ} (hbicolor : StrongPredecessorBicoloringAt k) :
    FractionalPredecessorCoverAt k := by
  intro n χ hreal hno
  obtain ⟨red, blue, _hdisjoint, hunion, hred, hblue⟩ :=
    hbicolor hreal hno
  let w : Finset (Fin n) → ℚ := fun support ↦
    (if support = red then 1 else 0) +
      (if support = blue then 1 else 0)
  have hwNonneg (support : Finset (Fin n)) : 0 ≤ w support := by
    dsimp [w]
    positivity
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · exact hwNonneg
  · intro support hpositive
    by_cases hsupportRed : support = red
    · simpa [hsupportRed] using hred
    · by_cases hsupportBlue : support = blue
      · simpa [hsupportBlue] using hblue
      · simp [w, hsupportRed, hsupportBlue] at hpositive
  · intro vertex
    let incidenceWeight : Finset (Fin n) → ℚ := fun support ↦
      if vertex ∈ support then w support else 0
    have hincidenceNonneg (support : Finset (Fin n)) :
        0 ≤ incidenceWeight support := by
      dsimp [incidenceWeight]
      by_cases hmem : vertex ∈ support
      · rw [if_pos hmem]
        exact hwNonneg support
      · rw [if_neg hmem]
    have hvertex : vertex ∈ red ∨ vertex ∈ blue := by
      rw [← Finset.mem_union]
      simp [hunion]
    rcases hvertex with hvertexRed | hvertexBlue
    · have hterm : incidenceWeight red ≤
          ∑ support : Finset (Fin n), incidenceWeight support :=
        Finset.single_le_sum
          (fun support (_ : support ∈ Finset.univ) ↦ hincidenceNonneg support)
          (Finset.mem_univ red)
      calc
        1 ≤ incidenceWeight red := by
          dsimp [incidenceWeight, w]
          rw [if_pos hvertexRed, if_pos rfl]
          by_cases hEq : red = blue <;> simp [hEq]
        _ ≤ _ := hterm
    · have hterm : incidenceWeight blue ≤
          ∑ support : Finset (Fin n), incidenceWeight support :=
        Finset.single_le_sum
          (fun support (_ : support ∈ Finset.univ) ↦ hincidenceNonneg support)
          (Finset.mem_univ blue)
      calc
        1 ≤ incidenceWeight blue := by
          dsimp [incidenceWeight, w]
          rw [if_pos hvertexBlue, if_pos rfl]
          by_cases hEq : blue = red <;> simp [hEq]
        _ ≤ _ := hterm
  · norm_num [w, Finset.sum_add_distrib]

/-- A fractional predecessor cover also contains one positive-weight support
holding at least half of the vertices. This is the unweighted averaging
consequence of the fractional cover inequalities. -/
theorem predecessorHalfSubsetAt_of_fractionalCover
    {k : ℕ} (hk : 2 ≤ k) (hfrac : FractionalPredecessorCoverAt k) :
    PredecessorHalfSubsetAt k := by
  intro n χ hreal hno
  obtain ⟨w, hnonneg, hfree, hcover, htotal⟩ := hfrac hreal hno
  by_cases hn : n = 0
  · subst n
    refine ⟨∅, ?_, by simp⟩
    rintro ⟨polygon, hpolygonSub, hpolygonCard, _⟩
    have hpolygon : polygon = ∅ := Finset.subset_empty.mp hpolygonSub
    subst polygon
    simp at hpolygonCard
    omega
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    by_contra hnone
    have hsmall (support : Finset (Fin n)) (hw : w support ≠ 0) :
        2 * support.card < n := by
      by_contra hnot
      apply hnone
      exact ⟨support, hfree support hw, by omega⟩
    have hpositive : ∃ support : Finset (Fin n), 0 < w support := by
      by_contra hnonePositive
      have hzero (support : Finset (Fin n)) : w support = 0 := by
        apply le_antisymm
        · exact le_of_not_gt fun hgt ↦ hnonePositive ⟨support, hgt⟩
        · exact hnonneg support
      have hcover0 := hcover (⟨0, hnpos⟩ : Fin n)
      simp [hzero] at hcover0
      norm_num at hcover0
    obtain ⟨strictSupport, hstrictPositive⟩ := hpositive
    have htermLe (support : Finset (Fin n)) :
        (((2 * support.card : ℕ) : ℚ) * w support) ≤
          (n : ℚ) * w support := by
      by_cases hw : w support = 0
      · simp [hw]
      · apply mul_le_mul_of_nonneg_right _ (hnonneg support)
        exact_mod_cast (hsmall support hw).le
    have htermLt :
        (((2 * strictSupport.card : ℕ) : ℚ) * w strictSupport) <
          (n : ℚ) * w strictSupport := by
      apply mul_lt_mul_of_pos_right _ hstrictPositive
      exact_mod_cast hsmall strictSupport hstrictPositive.ne'
    have hsumStrict :
        (∑ support : Finset (Fin n),
            ((2 * support.card : ℕ) : ℚ) * w support) <
          ∑ support : Finset (Fin n), (n : ℚ) * w support := by
      exact Finset.sum_lt_sum (fun support _ ↦ htermLe support)
        ⟨strictSupport, Finset.mem_univ _, htermLt⟩
    have hincidence :
        (n : ℚ) ≤ ∑ support : Finset (Fin n),
          (support.card : ℚ) * w support := by
      calc
        (n : ℚ) = ∑ _vertex : Fin n, (1 : ℚ) := by simp
        _ ≤ ∑ vertex : Fin n, ∑ support : Finset (Fin n),
            if vertex ∈ support then w support else 0 := by
          exact Finset.sum_le_sum fun vertex _ ↦ hcover vertex
        _ = ∑ support : Finset (Fin n),
            (support.card : ℚ) * w support := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro support _
          simp [nsmul_eq_mul]
    have hscaledStrict :
        (2 : ℚ) * (∑ support : Finset (Fin n),
            (support.card : ℚ) * w support) <
          (n : ℚ) * ∑ support : Finset (Fin n), w support := by
      calc
        (2 : ℚ) * (∑ support : Finset (Fin n),
            (support.card : ℚ) * w support) =
            ∑ support : Finset (Fin n),
              ((2 * support.card : ℕ) : ℚ) * w support := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro support _
                push_cast
                ring
        _ < ∑ support : Finset (Fin n), (n : ℚ) * w support := hsumStrict
        _ = (n : ℚ) * ∑ support : Finset (Fin n), w support := by
          rw [Finset.mul_sum]
    have hincidenceScaled :
        (2 : ℚ) * n ≤ (2 : ℚ) *
          ∑ support : Finset (Fin n), (support.card : ℚ) * w support :=
      mul_le_mul_of_nonneg_left hincidence (by norm_num)
    have htotalScaled :
        (n : ℚ) * ∑ support : Finset (Fin n), w support ≤ (n : ℚ) * 2 :=
      mul_le_mul_of_nonneg_left htotal (by positivity)
    linarith

/-- A fractional predecessor cover gives the same exact doubling recurrence
as an integral bicoloring. The proof is finite rational double counting: each
positive-weight predecessor-free support has bounded cardinality, while the
cover supplies total vertex incidence at least the ambient cardinality. -/
theorem sweepExactUpperAt_of_fractionalPredecessorCover
    {k : ℕ} (hk : 4 ≤ k)
    (hprev : SweepExactUpperAt (k - 1))
    (hfrac : FractionalPredecessorCoverAt k) :
    SweepExactUpperAt k := by
  intro n χ hreal hcard
  by_contra hno
  obtain ⟨w, hnonneg, hfree, hcover, htotal⟩ := hfrac hreal hno
  have hsupportCard (support : Finset (Fin n)) (hw : w support ≠ 0) :
      support.card ≤ 2 ^ (k - 3) := by
    by_contra hlarge
    have hstrict : 2 ^ ((k - 1) - 2) < support.card := by
      have hsub : (k - 1) - 2 = k - 3 := by omega
      rw [hsub]
      omega
    let e : Fin support.card ↪o Fin n := support.orderEmbOfFin rfl
    have hstrong := hprev (hreal.restrict e) hstrict
    have hmapped := containsStrongPolygonSet_map_restrict e hstrong
    rw [Finset.image_orderEmbOfFin_univ] at hmapped
    exact (hfree support hw) hmapped
  have hdouble :
      (n : ℚ) ≤ ((2 ^ (k - 3) : ℕ) : ℚ) * 2 := by
    calc
      (n : ℚ) = ∑ _vertex : Fin n, (1 : ℚ) := by simp
      _ ≤ ∑ vertex : Fin n, ∑ support : Finset (Fin n),
          if vertex ∈ support then w support else 0 := by
        exact Finset.sum_le_sum fun vertex _ ↦ hcover vertex
      _ = ∑ support : Finset (Fin n),
          (support.card : ℚ) * w support := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro support _
        simp [nsmul_eq_mul]
      _ ≤ ∑ support : Finset (Fin n),
          ((2 ^ (k - 3) : ℕ) : ℚ) * w support := by
        apply Finset.sum_le_sum
        intro support _
        by_cases hw : w support = 0
        · simp [hw]
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast hsupportCard support hw) (hnonneg support)
      _ = ((2 ^ (k - 3) : ℕ) : ℚ) *
          ∑ support : Finset (Fin n), w support := by
        rw [Finset.mul_sum]
      _ ≤ ((2 ^ (k - 3) : ℕ) : ℚ) * 2 :=
        mul_le_mul_of_nonneg_left htotal (by positivity)
  have hn : n ≤ 2 ^ (k - 3) * 2 := by
    exact_mod_cast hdouble
  have hkpow : k - 2 = (k - 3) + 1 := by omega
  rw [hkpow, pow_succ] at hcard
  omega

end ErdosSzekeres

end
