module

public import ErdosSzekeres.SukCyclicSupportContraction
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Clockwise periodization of a finite convex point set

Convex position makes the clockwise orientation relation around any chosen
vertex a strict total order on the remaining original points.  Enumerating
that order, prepending the chosen vertex, and reducing indices modulo the
cardinality gives the periodic strict-cap sequence needed by the cyclic
Pór--Valtr interface.  No coordinate sort or carrier transformation is used.
-/

namespace ErdosSzekeres

noncomputable section

/-- A private indexing wrapper, used so the angular order is not confused with
the point type's coordinatewise order.  Its value is still an original point. -/
private structure ClockwiseOrderedPoint (s : Finset (Point 2)) where
  val : s
  deriving Fintype

private def clockwiseOrderedPointEquiv (s : Finset (Point 2)) :
    ClockwiseOrderedPoint s ≃ s where
  toFun p := p.val
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

private theorem orientation_four_term_identity (a p q r : Point 2) :
    orientation p q r =
      orientation a p q + orientation a q r - orientation a p r := by
  simp only [orientation]
  ring

private theorem anchor_orientation_trans_of_convex
    (Y : Finset (Point 2)) (hconv : InConvexPosition Y)
    (hgp : InGeneralPosition Y)
    {a p q r : Point 2}
    (ha : a ∈ Y) (hp : p ∈ Y) (hq : q ∈ Y) (hr : r ∈ Y)
    (hapq : orientation a p q < 0)
    (haqr : orientation a q r < 0) :
    orientation a p r < 0 := by
  have hpa : p ≠ a := by
    intro h
    subst p
    simp at hapq
  have hqa : q ≠ a := by
    intro h
    subst q
    simp at hapq
  have hra : r ≠ a := by
    intro h
    subst r
    simp at haqr
  have hpq : p ≠ q := by
    intro h
    subst q
    simp at hapq
  have hqr : q ≠ r := by
    intro h
    subst r
    simp at haqr
  have hpr : p ≠ r := by
    intro h
    subst r
    rw [orientation_swap_last] at haqr
    linarith
  have hapr_ne : orientation a p r ≠ 0 :=
    hgp ha hp hr hpa.symm hra.symm hpr
  rcases lt_or_gt_of_ne hapr_ne with hapr | hapr
  · exact hapr
  · exfalso
    have hpqr : orientation p q r < 0 := by
      rw [orientation_four_term_identity a p q r]
      linarith
    have haTriangle : a ∈ convexHull ℝ (triangle p q r) :=
      (mem_convexHull_triangle_iff_of_orientation_neg p q r a hpqr).2 <| by
        constructor
        · rw [orientation_cyclic a p q]
          exact hapq.le
        constructor
        · rw [orientation_cyclic a q r]
          exact haqr.le
        · rw [orientation_cyclic a r p, orientation_swap_last a p r]
          linarith
    apply (hconv a ha)
    apply convexHull_mono _ haTriangle
    intro x hx
    simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hpa, hp⟩
    · exact Finset.mem_erase.mpr ⟨hqa, hq⟩
    · exact Finset.mem_erase.mpr ⟨hra, hr⟩

private theorem triple_orientation_neg_of_anchor
    (Y : Finset (Point 2)) (hconv : InConvexPosition Y)
    (hgp : InGeneralPosition Y)
    {a p q r : Point 2}
    (ha : a ∈ Y) (hp : p ∈ Y) (hq : q ∈ Y) (hr : r ∈ Y)
    (hapq : orientation a p q < 0)
    (hapr : orientation a p r < 0)
    (haqr : orientation a q r < 0) :
    orientation p q r < 0 := by
  have haq : a ≠ q := by
    intro h
    subst q
    simp at hapq
  have hpq : p ≠ q := by
    intro h
    subst q
    simp at hapq
  have hpr : p ≠ r := by
    intro h
    subst r
    simp at hapr
  have hqr : q ≠ r := by
    intro h
    subst r
    simp at haqr
  have hpqr_ne : orientation p q r ≠ 0 :=
    hgp hp hq hr hpq hpr hqr
  rcases lt_or_gt_of_ne hpqr_ne with hpqr | hpqr
  · exact hpqr
  · exfalso
    have hqTriangle : q ∈ convexHull ℝ (triangle a p r) :=
      (mem_convexHull_triangle_iff_of_orientation_neg a p r q hapr).2 <| by
        constructor
        · exact hapq.le
        constructor
        · rw [orientation_swap_last p q r]
          linarith
        · rw [orientation_cyclic' a q r]
          exact haqr.le
    apply (hconv q hq)
    apply convexHull_mono _ hqTriangle
    intro x hx
    simp only [triangle, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_erase.mpr ⟨haq, ha⟩
    · exact Finset.mem_erase.mpr ⟨hpq, hp⟩
    · exact Finset.mem_erase.mpr ⟨hqr.symm, hr⟩

/-- A finite planar set in general and convex position admits a clockwise
strict-cap enumeration of its original carrier, periodically extended. -/
theorem exists_clockwiseStrictCapPeriodization
    (Y : Finset (Point 2)) (m : ℕ)
    (hm : 3 ≤ m)
    (hcard : Y.card = m)
    (hconv : InConvexPosition Y)
    (hgp : InGeneralPosition Y) :
    ∃ anchors : ℕ → Point 2,
      SukStrictCapSequence m anchors ∧
      (∀ i, anchors (i + m) = anchors i) ∧
      (∀ i, i < m → anchors i ∈ Y) ∧
      (Finset.range m).image anchors = Y := by
  classical
  have hmpos : 0 < m := by omega
  have hYpos : 0 < Y.card := by omega
  obtain ⟨a, haY⟩ := Finset.card_pos.mp hYpos
  let rest : Finset (Point 2) := Y.erase a
  have hrestcard : rest.card = m - 1 := by
    dsimp [rest]
    rw [Finset.card_erase_of_mem haY, hcard]

  let clockwise (p q : ClockwiseOrderedPoint rest) : Prop :=
    orientation a p.val.1 q.val.1 < 0
  letI : DecidableRel clockwise := Classical.decRel _

  have hpair_ne (p q : ClockwiseOrderedPoint rest) (hpq : p ≠ q) :
      orientation a p.val.1 q.val.1 ≠ 0 := by
    have hap : a ≠ p.val.1 := (Finset.ne_of_mem_erase p.val.property).symm
    have haq : a ≠ q.val.1 := (Finset.ne_of_mem_erase q.val.property).symm
    have hpq' : p.val.1 ≠ q.val.1 := by
      intro h
      apply hpq
      apply (clockwiseOrderedPointEquiv rest).injective
      exact Subtype.ext h
    exact hgp haY (Finset.mem_of_mem_erase p.val.property)
      (Finset.mem_of_mem_erase q.val.property) hap haq hpq'

  letI : IsStrictTotalOrder (ClockwiseOrderedPoint rest) clockwise := {
    irrefl p := by simp [clockwise]
    trans p q r hpq hqr := by
      exact anchor_orientation_trans_of_convex Y hconv hgp
        haY (Finset.mem_of_mem_erase p.val.property)
        (Finset.mem_of_mem_erase q.val.property)
        (Finset.mem_of_mem_erase r.val.property) hpq hqr
    trichotomous p q hpq hqp := by
      by_contra hne
      rcases lt_or_gt_of_ne (hpair_ne p q hne) with hpqNeg | hpqPos
      · exact hpq hpqNeg
      · apply hqp
        change orientation a q.val.1 p.val.1 < 0
        rw [orientation_swap_last]
        linarith
  }

  letI : LinearOrder (ClockwiseOrderedPoint rest) := linearOrderOfSTO clockwise
  have horderedCard : Fintype.card (ClockwiseOrderedPoint rest) = m - 1 := by
    rw [Fintype.card_congr (clockwiseOrderedPointEquiv rest), Fintype.card_coe]
    exact hrestcard
  have hunivcard :
      (Finset.univ : Finset (ClockwiseOrderedPoint rest)).card = m - 1 := by
    simpa only [Finset.card_univ] using horderedCard
  let e : Fin (m - 1) ↪o ClockwiseOrderedPoint rest :=
    (Finset.univ : Finset (ClockwiseOrderedPoint rest)).orderEmbOfFin hunivcard

  have horderedTriple (p q r : ClockwiseOrderedPoint rest)
      (hpq : p < q) (hqr : q < r) :
      orientation p.val.1 q.val.1 r.val.1 < 0 := by
    have hpr : p < r := lt_trans hpq hqr
    change clockwise p q at hpq
    change clockwise q r at hqr
    change clockwise p r at hpr
    exact triple_orientation_neg_of_anchor Y hconv hgp
      haY (Finset.mem_of_mem_erase p.val.property)
      (Finset.mem_of_mem_erase q.val.property)
      (Finset.mem_of_mem_erase r.val.property) hpq hpr hqr

  let tail : Fin (m - 1) → Point 2 := fun i => (e i).val.1
  let sequence : Fin (m - 1 + 1) → Point 2 := Fin.cons a tail
  have hmcast : m - 1 + 1 = m := by omega

  have htailInjective : Function.Injective tail := by
    intro i j hij
    apply e.injective
    apply (clockwiseOrderedPointEquiv rest).injective
    exact Subtype.ext hij
  have haNotRange : a ∉ Set.range tail := by
    rintro ⟨i, hi⟩
    have hne : (e i).val.1 ≠ a := Finset.ne_of_mem_erase (e i).val.property
    exact hne hi
  have hsequenceInjective : Function.Injective sequence := by
    dsimp [sequence]
    exact Fin.cons_injective_of_injective haNotRange htailInjective

  have hsequenceMem (i : Fin (m - 1 + 1)) : sequence i ∈ Y := by
    cases i using Fin.cases with
    | zero => simpa [sequence] using haY
    | succ i =>
        simpa [sequence, tail] using Finset.mem_of_mem_erase (e i).val.property

  have hsequenceCap (i j k : Fin (m - 1 + 1))
      (hij : i < j) (hjk : j < k) :
      orientation (sequence i) (sequence j) (sequence k) < 0 := by
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j =>
            cases k using Fin.cases with
            | zero => simp at hjk
            | succ k =>
                have hjk' : j < k := by simpa using hjk
                have hrel := e.strictMono hjk'
                change clockwise (e j) (e k) at hrel
                simpa [sequence, tail, clockwise] using hrel
    | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j =>
            cases k using Fin.cases with
            | zero => simp at hjk
            | succ k =>
                have hij' : i < j := by simpa using hij
                have hjk' : j < k := by simpa using hjk
                simpa [sequence, tail] using
                  horderedTriple (e i) (e j) (e k)
                    (e.strictMono hij') (e.strictMono hjk')

  let anchors : ℕ → Point 2 := fun i =>
    sequence (Fin.cast hmcast.symm ⟨i % m, Nat.mod_lt i hmpos⟩)
  refine ⟨anchors, ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk hkm
    have him : i < m := by omega
    have hjm : j < m := by omega
    have hiMod : i % m = i := Nat.mod_eq_of_lt him
    have hjMod : j % m = j := Nat.mod_eq_of_lt hjm
    have hkMod : k % m = k := Nat.mod_eq_of_lt hkm
    apply hsequenceCap
    · simpa [hiMod, hjMod] using hij
    · simpa [hjMod, hkMod] using hjk
  · intro i
    apply congrArg sequence
    apply Fin.ext
    simp
  · intro i _hi
    exact hsequenceMem _
  · have hsubset : (Finset.range m).image anchors ⊆ Y := by
      intro p hp
      simp only [Finset.mem_image, Finset.mem_range] at hp
      obtain ⟨i, _hi, rfl⟩ := hp
      exact hsequenceMem _
    have hinjective : Set.InjOn anchors (Finset.range m) := by
      intro i hi j hj hij
      have hi' : i < m := Finset.mem_range.mp hi
      have hj' : j < m := Finset.mem_range.mp hj
      have hfin : (⟨i, hi'⟩ : Fin m) = ⟨j, hj'⟩ := by
        apply Fin.cast_injective hmcast.symm
        apply hsequenceInjective
        simpa [anchors, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] using hij
      exact congrArg Fin.val hfin
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hcard, Finset.card_image_of_injOn hinjective, Finset.card_range]

end

end ErdosSzekeres

end
