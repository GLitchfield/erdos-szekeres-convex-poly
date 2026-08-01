import ErdosSzekeres.Extremal
import Mathlib.Data.Nat.Find

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

end FinsetPolygon

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
