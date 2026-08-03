module

public import ErdosSzekeres.E3State466Certificate
public import ErdosSzekeres.E3State566Certificate

@[expose] public section

/-!
# Finite off-diagonal states for E3

This module packages the three-parameter finite states used by the proposed
repair of the decomposable-set induction.  A state bound is hereditary: it is
stated for an arbitrary decomposable subset, rather than only for a coloring
whose whole vertex type has one fixed size.
-/

namespace ErdosSzekeres

namespace Turn

/-- Exchange the two colors of a triple coloring. -/
def dual : Turn → Turn
  | .left => .right
  | .right => .left

@[simp] theorem dual_left : dual .left = .right := rfl

@[simp] theorem dual_right : dual .right = .left := rfl

@[simp] theorem dual_dual (c : Turn) : dual (dual c) = c := by
  cases c <;> rfl

theorem dual_injective : Function.Injective dual := by
  intro a b hab
  simpa only [dual_dual] using congrArg dual hab

end Turn

namespace TripleColoring

/-- Pointwise color duality. -/
def dual {n : ℕ} (χ : TripleColoring n) : TripleColoring n :=
  fun t => Turn.dual (χ t)

@[simp] theorem dual_apply {n : ℕ} (χ : TripleColoring n)
    (t : OrderedTriple n) : χ.dual t = Turn.dual (χ t) := rfl

end TripleColoring

/-- The off-diagonal E3 bound at `(a,u,k)`: every decomposable set larger than
the proposed threshold has an `a`-cap, a `u`-cup, or a strong `k`-set. -/
def DecomposableStateUpper (a u k : ℕ) : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)},
    IsDecomposableOn χ s → decomposableThreshold a u k < s.card →
      ContainsCapSet χ s a ∨ ContainsCupSet χ s u ∨
        ContainsStrongPolygonSet χ s k

/-- Color duality exchanges the two sides of a deep-below split. -/
theorem HasDeepBelowSplit.dual {n : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)} (h : HasDeepBelowSplit χ lower upper) :
    HasDeepBelowSplit χ.dual upper lower := by
  refine ⟨h.disjoint.symm, ?_⟩
  intro t hi hj hk hnotUpper hnotLower
  have hi' : t.i ∈ lower ∪ upper := by simpa [Finset.union_comm] using hi
  have hj' : t.j ∈ lower ∪ upper := by simpa [Finset.union_comm] using hj
  have hk' : t.k ∈ lower ∪ upper := by simpa [Finset.union_comm] using hk
  have hcolor := h.crossing t hi' hj' hk' hnotLower hnotUpper
  have hdisjoint := Finset.disjoint_left.mp h.disjoint
  by_cases hjLower : t.j ∈ lower
  · have hjNotUpper : t.j ∉ upper := fun hjUpper => hdisjoint hjLower hjUpper
    simp [TripleColoring.dual, hcolor, hjLower, hjNotUpper, Turn.dual]
  · have hjUpper : t.j ∈ upper := by
      rcases Finset.mem_union.mp hj' with hmem | hmem
      · exact (hjLower hmem).elim
      · exact hmem
    simp [TripleColoring.dual, hcolor, hjLower, hjUpper, Turn.dual]

/-- Recursive decomposability is invariant under color duality. -/
theorem IsDecomposableOn.dual {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} (h : IsDecomposableOn χ s) :
    IsDecomposableOn χ.dual s := by
  induction h with
  | singleton i => exact .singleton i
  | @split lower upper hlower hupper hdeep ihlower ihupper =>
      simpa [Finset.union_comm] using
        IsDecomposableOn.split ihupper ihlower hdeep.dual

/-- Cups for the dual coloring are caps for the original coloring. -/
theorem isCupSet_dual_iff {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : IsCupSet χ.dual s ↔ IsCapSet χ s := by
  constructor <;> intro h t hi hj hk
  · have ht := h t hi hj hk
    cases hχ : χ t <;> simp_all [TripleColoring.dual, Turn.dual]
  · simp [TripleColoring.dual, Turn.dual, h t hi hj hk]

/-- Caps for the dual coloring are cups for the original coloring. -/
theorem isCapSet_dual_iff {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : IsCapSet χ.dual s ↔ IsCupSet χ s := by
  constructor <;> intro h t hi hj hk
  · have ht := h t hi hj hk
    cases hχ : χ t <;> simp_all [TripleColoring.dual, Turn.dual]
  · simp [TripleColoring.dual, Turn.dual, h t hi hj hk]

/-- The strong-polygon law is invariant under exchanging its two colors. -/
theorem isStrongPolygonSet_dual_iff {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} :
    IsStrongPolygonSet χ.dual s ↔ IsStrongPolygonSet χ s := by
  constructor
  · intro h i j k l hij hjk hkl hi hj hk hl
    obtain ⟨h₁, h₂⟩ := h hij hjk hkl hi hj hk hl
    exact ⟨Turn.dual_injective h₁, Turn.dual_injective h₂⟩
  · intro h i j k l hij hjk hkl hi hj hk hl
    obtain ⟨h₁, h₂⟩ := h hij hjk hkl hi hj hk hl
    exact ⟨congrArg Turn.dual h₁, congrArg Turn.dual h₂⟩

theorem containsCupSet_dual_iff {n u : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : ContainsCupSet χ.dual s u ↔ ContainsCapSet χ s u := by
  constructor
  · rintro ⟨cup, hsub, hcard, hcup⟩
    exact ⟨cup, hsub, hcard, isCupSet_dual_iff.mp hcup⟩
  · rintro ⟨cap, hsub, hcard, hcap⟩
    exact ⟨cap, hsub, hcard, isCupSet_dual_iff.mpr hcap⟩

theorem containsCapSet_dual_iff {n a : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} : ContainsCapSet χ.dual s a ↔ ContainsCupSet χ s a := by
  constructor
  · rintro ⟨cap, hsub, hcard, hcap⟩
    exact ⟨cap, hsub, hcard, isCapSet_dual_iff.mp hcap⟩
  · rintro ⟨cup, hsub, hcard, hcup⟩
    exact ⟨cup, hsub, hcard, isCapSet_dual_iff.mpr hcup⟩

theorem containsStrongPolygonSet_dual_iff {n k : ℕ}
    {χ : TripleColoring n} {s : Finset (Fin n)} :
    ContainsStrongPolygonSet χ.dual s k ↔ ContainsStrongPolygonSet χ s k := by
  constructor
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    exact ⟨polygon, hsub, hcard, isStrongPolygonSet_dual_iff.mp hstrong⟩
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    exact ⟨polygon, hsub, hcard, isStrongPolygonSet_dual_iff.mpr hstrong⟩

/-- Every nonempty finite set contains a one-vertex cup. -/
theorem containsCupSet_one {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} (hs : s.Nonempty) : ContainsCupSet χ s 1 := by
  obtain ⟨x, hx⟩ := hs
  refine ⟨{x}, by simpa using hx, by simp, ?_⟩
  intro t hi hj _
  simp only [Finset.mem_singleton] at hi hj
  exact ((ne_of_lt t.hij) (hi.trans hj.symm)).elim

/-- Every nonempty finite set contains a one-vertex cap. -/
theorem containsCapSet_one {n : ℕ} {χ : TripleColoring n}
    {s : Finset (Fin n)} (hs : s.Nonempty) : ContainsCapSet χ s 1 := by
  obtain ⟨x, hx⟩ := hs
  refine ⟨{x}, by simpa using hx, by simp, ?_⟩
  intro t hi hj _
  simp only [Finset.mem_singleton] at hi hj
  exact ((ne_of_lt t.hij) (hi.trans hj.symm)).elim

/-- Package the crossing cup--cap construction when the two chains are
presented through the existential `Contains...` predicates. -/
theorem HasDeepBelowSplit.containsStrongPolygonSet_of_containsCupCap
    {n u a k : ℕ} {χ : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper)
    (hcup : ContainsCupSet χ lower u)
    (hcap : ContainsCapSet χ upper a) (hcard : k ≤ u + a) :
    ContainsStrongPolygonSet χ (lower ∪ upper) k := by
  obtain ⟨cup, hcupSub, hcupCard, hcupMono⟩ := hcup
  obtain ⟨cap, hcapSub, hcapCard, hcapMono⟩ := hcap
  apply h.containsStrongPolygonSet_of_cup_cap hcupSub hcapSub hcupMono hcapMono
  simpa [hcupCard, hcapCard] using hcard

@[simp] theorem decomposableThreshold_state466 :
    decomposableThreshold 4 6 6 = 11 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow,
    Finset.sum_Icc_succ_top, Nat.choose]

@[simp] theorem decomposableThreshold_state646 :
    decomposableThreshold 6 4 6 = 11 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow,
    Finset.sum_Icc_succ_top, Nat.choose]

@[simp] theorem decomposableThreshold_state566 :
    decomposableThreshold 5 6 6 = 15 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow,
    Finset.sum_Icc_succ_top, Nat.choose]

@[simp] theorem decomposableThreshold_state656 :
    decomposableThreshold 6 5 6 = 15 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow,
    Finset.sum_Icc_succ_top, Nat.choose]

/-- The kernel-checked twelve-vertex certificate proves the hereditary
`(4,6,6)` state required by the E3 induction. -/
theorem decomposableStateUpper_466 : DecomposableStateUpper 4 6 6 := by
  intro n χ s hdecomposable hcard
  rw [decomposableThreshold_state466] at hcard
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (show 12 ≤ s.card by omega)
  let e : Fin 12 ↪o Fin n := t.orderEmbOfFin htcard
  let ψ : TripleColoring 12 := χ.restrict e
  have he_mem (i : Fin 12) : e i ∈ s :=
    hts (t.orderEmbOfFin_mem htcard i)
  have hallowed : ∀ (a b c d : Fin 12),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (ψ ⟨a, b, c, hab, hbc⟩)
        (ψ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (ψ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (ψ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    simpa [ψ, TripleColoring.restrict, OrderedTriple.map] using
      hdecomposable.turnSequenceAllowed (e.strictMono hab) (e.strictMono hbc)
        (e.strictMono hcd) (he_mem a) (he_mem b) (he_mem c) (he_mem d)
  rcases exists_cap_four_or_cup_six_or_strong_six ψ hallowed with
      ⟨f, hcap⟩ | ⟨f, hcup⟩ | ⟨f, hstrong⟩
  · let g : Fin 4 ↪o Fin n := f.trans e
    let cap := Finset.univ.image g
    refine Or.inl ⟨cap, ?_, ?_, ?_⟩
    · intro x hx
      simp only [cap, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCap χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcap
      exact FinsetPolygon.IsCap.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let cup := Finset.univ.image g
    refine Or.inr (Or.inl ⟨cup, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [cup, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCup χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcup
      exact FinsetPolygon.IsCup.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let polygon := Finset.univ.image g
    refine Or.inr (Or.inr ⟨polygon, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [polygon, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsStrongPolygonOn χ g := by
        intro i j k l hij hjk hkl
        simpa [g, ψ, IsStrongPolygonOn, TripleColoring.restrict,
          OrderedTriple.map] using hstrong hij hjk hkl
      exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hmap

/-- The color-dual form of the certified `(4,6,6)` state. -/
theorem decomposableStateUpper_646 : DecomposableStateUpper 6 4 6 := by
  intro n χ s hdecomposable hcard
  rw [decomposableThreshold_state646] at hcard
  have hcard' : decomposableThreshold 4 6 6 < s.card := by simpa using hcard
  rcases decomposableStateUpper_466 hdecomposable.dual hcard' with
      hcap | hcup | hstrong
  · exact Or.inr (Or.inl (containsCapSet_dual_iff.mp hcap))
  · exact Or.inl (containsCupSet_dual_iff.mp hcup)
  · exact Or.inr (Or.inr (containsStrongPolygonSet_dual_iff.mp hstrong))

/-- The `(5,6,6)` state implies its color-dual `(6,5,6)` state. -/
theorem decomposableStateUpper_656_of_state566
    (h566 : DecomposableStateUpper 5 6 6) :
    DecomposableStateUpper 6 5 6 := by
  intro n χ s hdecomposable hcard
  rw [decomposableThreshold_state656] at hcard
  have hcard' : decomposableThreshold 5 6 6 < s.card := by simpa using hcard
  rcases h566 hdecomposable.dual hcard' with hcap | hcup | hstrong
  · exact Or.inr (Or.inl (containsCapSet_dual_iff.mp hcap))
  · exact Or.inl (containsCupSet_dual_iff.mp hcup)
  · exact Or.inr (Or.inr (containsStrongPolygonSet_dual_iff.mp hstrong))

/-- The finite sixteen-vertex statement needed for the hereditary `(5,6,6)`
state.  It is deliberately independent of the certificate representation. -/
def State566FiniteUpper : Prop :=
  ∀ (χ : TripleColoring 16),
    (∀ (a b c d : Fin 16),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (χ ⟨a, b, c, hab, hbc⟩)
        (χ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (χ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (χ ⟨b, c, d, hbc, hcd⟩)) →
      (∃ f : Fin 5 ↪o Fin 16, IsCap χ f) ∨
      (∃ f : Fin 6 ↪o Fin 16, IsCup χ f) ∨
      (∃ f : Fin 6 ↪o Fin 16, IsStrongPolygonOn χ f)

/-- A proof of the finite sixteen-vertex statement lifts to the hereditary
`(5,6,6)` state.  This theorem audits the restriction and witness-transport
part of the SAT-to-E3 bridge without depending on any SAT encoding. -/
theorem decomposableStateUpper_566_of_finite
    (hfinite : State566FiniteUpper) : DecomposableStateUpper 5 6 6 := by
  intro n χ s hdecomposable hcard
  rw [decomposableThreshold_state566] at hcard
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq (show 16 ≤ s.card by omega)
  let e : Fin 16 ↪o Fin n := t.orderEmbOfFin htcard
  let ψ : TripleColoring 16 := χ.restrict e
  have he_mem (i : Fin 16) : e i ∈ s :=
    hts (t.orderEmbOfFin_mem htcard i)
  have hallowed : ∀ (a b c d : Fin 16),
      ∀ (hab : a < b) (hbc : b < c) (hcd : c < d),
      TurnSequenceAllowed
        (ψ ⟨a, b, c, hab, hbc⟩)
        (ψ ⟨a, b, d, hab, hbc.trans hcd⟩)
        (ψ ⟨a, c, d, hab.trans hbc, hcd⟩)
        (ψ ⟨b, c, d, hbc, hcd⟩) := by
    intro a b c d hab hbc hcd
    simpa [ψ, TripleColoring.restrict, OrderedTriple.map] using
      hdecomposable.turnSequenceAllowed (e.strictMono hab) (e.strictMono hbc)
        (e.strictMono hcd) (he_mem a) (he_mem b) (he_mem c) (he_mem d)
  rcases hfinite ψ hallowed with
      ⟨f, hcap⟩ | ⟨f, hcup⟩ | ⟨f, hstrong⟩
  · let g : Fin 5 ↪o Fin n := f.trans e
    let cap := Finset.univ.image g
    refine Or.inl ⟨cap, ?_, ?_, ?_⟩
    · intro x hx
      simp only [cap, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCap χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcap
      exact FinsetPolygon.IsCap.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let cup := Finset.univ.image g
    refine Or.inr (Or.inl ⟨cup, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [cup, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsCup χ g := by
        simpa [g, ψ, Function.comp_def] using
          IsMonochromaticChain.map_of_restrict_eq e rfl hcup
      exact FinsetPolygon.IsCup.image hmap
  · let g : Fin 6 ↪o Fin n := f.trans e
    let polygon := Finset.univ.image g
    refine Or.inr (Or.inr ⟨polygon, ?_, ?_, ?_⟩)
    · intro x hx
      simp only [polygon, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact he_mem (f i)
    · exact (Finset.card_image_of_injective _ g.injective).trans (by simp)
    · have hmap : IsStrongPolygonOn χ g := by
        intro i j k l hij hjk hkl
        simpa [g, ψ, IsStrongPolygonOn, TripleColoring.restrict,
          OrderedTriple.map] using hstrong hij hjk hkl
      exact FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hmap

/-- The checkpointed LRAT certificate, after its generated semantic bridge,
proves the representation-independent sixteen-vertex finite statement. -/
theorem state566FiniteUpper : State566FiniteUpper := by
  intro χ hallowed
  exact exists_cap_five_or_cup_six_or_strong_six χ hallowed

/-- The remaining hereditary finite state for the decomposable `k = 6`
upper bound.  Its threshold is fifteen, so the finite core has sixteen
vertices. -/
theorem decomposableStateUpper_566 : DecomposableStateUpper 5 6 6 :=
  decomposableStateUpper_566_of_finite state566FiniteUpper

/-- At `k = 6`, the certified `(4,6,6)` state and its dual reduce the exact
decomposable upper bound to the single next off-diagonal state `(5,6,6)`.

This is the fixed E3 finite-reduction target: the autonomous proof work may
introduce helper declarations, but must not strengthen this theorem's
assumption or weaken its conclusion. -/
theorem decomposableExactUpperAt_six_of_state566
    (h566 : DecomposableStateUpper 5 6 6) :
    DecomposableExactUpperAt 6 := by
  intro n χ hsweep hdecomposable hn
  norm_num at hn
  by_contra hno
  change IsDecomposableOn χ Finset.univ at hdecomposable
  have htwo : 2 ≤ (Finset.univ : Finset (Fin n)).card := by simp; omega
  obtain ⟨lower, upper, hlowerNonempty, hupperNonempty,
      hlower, hupper, hdeep, hunion⟩ := hdecomposable.exists_split htwo
  have hnoRoot : ¬ContainsStrongPolygonSet χ (lower ∪ upper) 6 := by
    simpa only [← hunion] using hno
  have hnoStrongLower : ¬ContainsStrongPolygonSet χ lower 6 := by
    intro h
    exact hnoRoot
      (FinsetPolygon.ContainsStrongPolygonSet.mono h Finset.subset_union_left)
  have hnoStrongUpper : ¬ContainsStrongPolygonSet χ upper 6 := by
    intro h
    exact hnoRoot
      (FinsetPolygon.ContainsStrongPolygonSet.mono h Finset.subset_union_right)
  have hnoCupSixLower : ¬ContainsCupSet χ lower 6 := by
    intro h
    exact hnoStrongLower
      (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet h)
  have hnoCupSixUpper : ¬ContainsCupSet χ upper 6 := by
    intro h
    exact hnoStrongUpper
      (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet h)
  have hnoCapSixLower : ¬ContainsCapSet χ lower 6 := by
    intro h
    exact hnoStrongLower
      (FinsetPolygon.ContainsCapSet.toContainsStrongPolygonSet h)
  have hnoCapSixUpper : ¬ContainsCapSet χ upper 6 := by
    intro h
    exact hnoStrongUpper
      (FinsetPolygon.ContainsCapSet.toContainsStrongPolygonSet h)
  have htotal : 16 < lower.card + upper.card := by
    have hcardUnion := Finset.card_union_of_disjoint hdeep.disjoint
    rw [← hcardUnion, ← hunion]
    simpa using hn
  have upper_card_le_eleven
      (hnoCapFour : ¬ContainsCapSet χ upper 4) : upper.card ≤ 11 := by
    by_contra hcard
    have hlarge : decomposableThreshold 4 6 6 < upper.card := by simp; omega
    rcases decomposableStateUpper_466 hupper hlarge with hcap | hcup | hstrong
    · exact hnoCapFour hcap
    · exact hnoCupSixUpper hcup
    · exact hnoStrongUpper hstrong
  have lower_card_le_eleven
      (hnoCupFour : ¬ContainsCupSet χ lower 4) : lower.card ≤ 11 := by
    by_contra hcard
    have hlarge : decomposableThreshold 6 4 6 < lower.card := by simp; omega
    rcases decomposableStateUpper_646 hlower hlarge with hcap | hcup | hstrong
    · exact hnoCapSixLower hcap
    · exact hnoCupFour hcup
    · exact hnoStrongLower hstrong
  have h656 : DecomposableStateUpper 6 5 6 :=
    decomposableStateUpper_656_of_state566 (h566 := h566)
  by_cases hcupFour : ContainsCupSet χ lower 4
  · by_cases hcapFour : ContainsCapSet χ upper 4
    · exact hnoRoot
        (hdeep.containsStrongPolygonSet_of_containsCupCap hcupFour hcapFour (by omega))
    · have hupperEleven := upper_card_le_eleven hcapFour
      have hupperOne : upper.card ≤ 1 := by
        by_contra hcard
        have hlarge : Nat.choose (2 + 6 - 4) (2 - 2) < upper.card := by
          norm_num [Nat.choose]
          omega
        rcases containsCapSet_or_containsCupSet_of_choose_lt
            (a := 2) (u := 6) hsweep upper (by omega) (by omega) hlarge with
          hcapTwo | hcupSix
        · exact hnoRoot
            (hdeep.containsStrongPolygonSet_of_containsCupCap
              hcupFour hcapTwo (by omega))
        · exact hnoCupSixUpper hcupSix
      have hlowerLarge : decomposableThreshold 6 5 6 < lower.card := by
        simp
        omega
      rcases h656 hlower hlowerLarge with hcapSix | hcupFive | hstrong
      · exact hnoCapSixLower hcapSix
      · exact hnoRoot
          (hdeep.containsStrongPolygonSet_of_containsCupCap hcupFive
            (containsCapSet_one hupperNonempty) (by omega))
      · exact hnoStrongLower hstrong
  · by_cases hcapFour : ContainsCapSet χ upper 4
    · have hlowerEleven := lower_card_le_eleven hcupFour
      have hlowerOne : lower.card ≤ 1 := by
        by_contra hcard
        have hlarge : Nat.choose (6 + 2 - 4) (6 - 2) < lower.card := by
          norm_num [Nat.choose]
          omega
        rcases containsCapSet_or_containsCupSet_of_choose_lt
            (a := 6) (u := 2) hsweep lower (by omega) (by omega) hlarge with
          hcapSix | hcupTwo
        · exact hnoCapSixLower hcapSix
        · exact hnoRoot
            (hdeep.containsStrongPolygonSet_of_containsCupCap
              hcupTwo hcapFour (by omega))
      have hupperLarge : decomposableThreshold 5 6 6 < upper.card := by
        simp
        omega
      rcases h566 hupper hupperLarge with hcapFive | hcupSix | hstrong
      · exact hnoRoot
          (hdeep.containsStrongPolygonSet_of_containsCupCap
            (containsCupSet_one hlowerNonempty) hcapFive (by omega))
      · exact hnoCupSixUpper hcupSix
      · exact hnoStrongUpper hstrong
    · have hlowerEleven := lower_card_le_eleven hcupFour
      have hupperEleven := upper_card_le_eleven hcapFour
      by_cases hlowerFive : lower.card ≤ 5
      · omega
      · have hlowerLarge : Nat.choose (6 + 3 - 4) (6 - 2) < lower.card := by
          norm_num [Nat.choose]
          omega
        rcases containsCapSet_or_containsCupSet_of_choose_lt
            (a := 6) (u := 3) hsweep lower (by omega) (by omega) hlowerLarge with
          hcapSix | hcupThree
        · exact hnoCapSixLower hcapSix
        · by_cases hupperFive : upper.card ≤ 5
          · omega
          · have hupperLarge : Nat.choose (3 + 6 - 4) (3 - 2) < upper.card := by
              norm_num [Nat.choose]
              omega
            rcases containsCapSet_or_containsCupSet_of_choose_lt
                (a := 3) (u := 6) hsweep upper (by omega) (by omega) hupperLarge with
              hcapThree | hcupSix
            · exact hnoRoot
                (hdeep.containsStrongPolygonSet_of_containsCupCap
                  hcupThree hcapThree (by omega))
            · exact hnoCupSixUpper hcupSix

/-- The exact Erdős--Szekeres upper formula holds at `k = 6` throughout the
abstract recursively decomposable class. -/
theorem decomposableExactUpperAt_six : DecomposableExactUpperAt 6 :=
  decomposableExactUpperAt_six_of_state566 decomposableStateUpper_566

end ErdosSzekeres

end
