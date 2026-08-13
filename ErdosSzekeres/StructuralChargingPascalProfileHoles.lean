module

public import ErdosSzekeres.StructuralChargingPascalTails
public import ErdosSzekeres.StructuralChargingMiddleSplits

@[expose] public section

/-!
# Endpoint-middle profiles inside the Pascal window

This file isolates the local profile information supplied by a strong ordered
polygon.  It deliberately does not use a Pascal-tail estimate: the only
ingredients are middle determinacy and the absence of monochromatic subsets.
-/

namespace ErdosSzekeres

noncomputable section

/-- The first index of an ordered `s`-set. -/
def pascalProfileFirst {s : ℕ} (hs : 2 ≤ s) : Fin s :=
  ⟨0, by omega⟩

/-- The `i`th internal index of an ordered `s`-set. -/
def pascalProfileMiddle {s : ℕ} (hs : 2 ≤ s) (i : Fin (s - 2)) : Fin s :=
  ⟨i.1 + 1, by omega⟩

/-- The last index of an ordered `s`-set. -/
def pascalProfileLast {s : ℕ} (hs : 2 ≤ s) : Fin s :=
  ⟨s - 1, by omega⟩

theorem pascalProfileMiddle_injective {s : ℕ} (hs : 2 ≤ s) :
    Function.Injective (pascalProfileMiddle hs) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simp only [pascalProfileMiddle] at hval
  omega

theorem pascalProfile_first_lt_middle {s : ℕ} (hs : 2 ≤ s)
    (i : Fin (s - 2)) :
    pascalProfileFirst hs < pascalProfileMiddle hs i := by
  simp only [pascalProfileFirst, pascalProfileMiddle, Fin.mk_lt_mk]
  omega

theorem pascalProfile_middle_lt_last {s : ℕ} (hs : 2 ≤ s)
    (i : Fin (s - 2)) :
    pascalProfileMiddle hs i < pascalProfileLast hs := by
  simp only [pascalProfileMiddle, pascalProfileLast, Fin.mk_lt_mk]
  omega

/-- The color seen at the two endpoints and an internal middle position. -/
def strongPolygonEndpointMiddleColor {n s : ℕ} (hs : 2 ≤ s)
    (χ : TripleColoring n) (polygon : Finset (Fin n))
    (hcard : polygon.card = s) (i : Fin (s - 2)) : Turn :=
  let e := polygon.orderEmbOfFin hcard
  χ ⟨e (pascalProfileFirst hs), e (pascalProfileMiddle hs i),
    e (pascalProfileLast hs),
    e.strictMono (pascalProfile_first_lt_middle hs i),
    e.strictMono (pascalProfile_middle_lt_last hs i)⟩

/-- Internal positions whose endpoint-middle triple has color `c`. -/
def strongPolygonMiddleProfile {n s : ℕ} (hs : 2 ≤ s)
    (χ : TripleColoring n) (polygon : Finset (Fin n))
    (hcard : polygon.card = s) (c : Turn) : Finset (Fin (s - 2)) :=
  Finset.univ.filter fun i =>
    strongPolygonEndpointMiddleColor hs χ polygon hcard i = c

/-- The internal right-colored endpoint-middle positions. -/
abbrev strongPolygonRightMiddleProfile {n s : ℕ} (hs : 2 ≤ s)
    (χ : TripleColoring n) (polygon : Finset (Fin n))
    (hcard : polygon.card = s) : Finset (Fin (s - 2)) :=
  strongPolygonMiddleProfile hs χ polygon hcard Turn.right

/-- The internal left-colored endpoint-middle positions. -/
abbrev strongPolygonLeftMiddleProfile {n s : ℕ} (hs : 2 ≤ s)
    (χ : TripleColoring n) (polygon : Finset (Fin n))
    (hcard : polygon.card = s) : Finset (Fin (s - 2)) :=
  strongPolygonMiddleProfile hs χ polygon hcard Turn.left

/-- Add the two endpoints to a selected set of internal positions. -/
def pascalProfileEndpointSupport {s : ℕ} (hs : 2 ≤ s)
    (middle : Finset (Fin (s - 2))) : Finset (Fin s) :=
  insert (pascalProfileFirst hs)
    (insert (pascalProfileLast hs) (middle.image (pascalProfileMiddle hs)))

theorem pascalProfileEndpointSupport_card {s : ℕ} (hs : 2 ≤ s)
    (middle : Finset (Fin (s - 2))) :
    (pascalProfileEndpointSupport hs middle).card = middle.card + 2 := by
  have hfirstLast : pascalProfileFirst hs ≠ pascalProfileLast hs := by
    intro h
    have hval := congrArg Fin.val h
    simp only [pascalProfileFirst, pascalProfileLast] at hval
    omega
  have hfirstImage :
      pascalProfileFirst hs ∉ middle.image (pascalProfileMiddle hs) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i hi hEq
    have hval := congrArg Fin.val hEq
    simp only [pascalProfileFirst, pascalProfileMiddle] at hval
    omega
  have hlastImage :
      pascalProfileLast hs ∉ middle.image (pascalProfileMiddle hs) := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro i hi hEq
    have hval := congrArg Fin.val hEq
    simp only [pascalProfileLast, pascalProfileMiddle] at hval
    omega
  rw [pascalProfileEndpointSupport,
    Finset.card_insert_of_notMem (by simpa [hfirstLast] using hfirstImage),
    Finset.card_insert_of_notMem hlastImage,
    Finset.card_image_of_injective _ (pascalProfileMiddle_injective hs)]

/-- A selected endpoint-middle profile lifts to a monochromatic subset of the
strong polygon after adjoining its endpoints. -/
theorem strongPolygon_endpointSupport_isColor
    {n s : ℕ} {hs : 2 ≤ s} {χ : TripleColoring n}
    {polygon : Finset (Fin n)} {hcard : polygon.card = s}
    (hstrong : IsStrongPolygonSet χ polygon) (c : Turn)
    (middle : Finset (Fin (s - 2)))
    (hsub : middle ⊆ strongPolygonMiddleProfile hs χ polygon hcard c) :
    ∀ t : OrderedTriple n,
      t.i ∈ (pascalProfileEndpointSupport hs middle).image
        (polygon.orderEmbOfFin hcard) →
      t.j ∈ (pascalProfileEndpointSupport hs middle).image
        (polygon.orderEmbOfFin hcard) →
      t.k ∈ (pascalProfileEndpointSupport hs middle).image
        (polygon.orderEmbOfFin hcard) →
      χ t = c := by
  let e : Fin s ↪o Fin n := polygon.orderEmbOfFin hcard
  have heMem (i : Fin s) : e i ∈ polygon :=
    polygon.orderEmbOfFin_mem hcard i
  have hmiddleDetermined : IsMiddleDeterminedOn χ polygon :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
  intro t hi hj hk
  simp only [Finset.mem_image] at hi hj hk
  obtain ⟨i, hiSupport, hiEq⟩ := hi
  obtain ⟨j, hjSupport, hjEq⟩ := hj
  obtain ⟨k, hkSupport, hkEq⟩ := hk
  have hij : i < j := by
    apply e.lt_iff_lt.mp
    simpa only [e, hiEq, hjEq] using t.4
  have hjk : j < k := by
    apply e.lt_iff_lt.mp
    simpa only [e, hjEq, hkEq] using t.5
  have hjMiddle :
      j ∈ middle.image (pascalProfileMiddle hs) := by
    simp only [pascalProfileEndpointSupport, Finset.mem_insert] at hjSupport
    rcases hjSupport with hjFirst | hjLast | hjImage
    · have hnot : ¬ i < pascalProfileFirst hs := by
        change ¬i.1 < 0
        omega
      exact (hnot (hjFirst ▸ hij)).elim
    · have hnot : ¬ pascalProfileLast hs < k := by
        change ¬s - 1 < k.1
        omega
      exact (hnot (hjLast ▸ hjk)).elim
    · exact hjImage
  simp only [Finset.mem_image] at hjMiddle
  obtain ⟨q, hqMiddle, hqEq⟩ := hjMiddle
  subst j
  have hqProfile := hsub hqMiddle
  simp only [strongPolygonMiddleProfile, Finset.mem_filter,
    Finset.mem_univ, true_and] at hqProfile
  have hcolor := hmiddleDetermined
    (e.strictMono hij)
    (e.strictMono (pascalProfile_first_lt_middle hs q))
    (e.strictMono hjk)
    (e.strictMono (pascalProfile_middle_lt_last hs q))
    (heMem i) (heMem (pascalProfileFirst hs))
    (heMem (pascalProfileMiddle hs q)) (heMem k)
    (heMem (pascalProfileLast hs))
  simpa only [e, hiEq, hjEq, hkEq] using hcolor.trans hqProfile

theorem strongPolygonMiddleProfile_partition
    {n s : ℕ} (hs : 2 ≤ s) (χ : TripleColoring n)
    (polygon : Finset (Fin n)) (hcard : polygon.card = s) :
    (strongPolygonRightMiddleProfile hs χ polygon hcard).card +
        (strongPolygonLeftMiddleProfile hs χ polygon hcard).card = s - 2 := by
  have hdisjoint : Disjoint
      (strongPolygonRightMiddleProfile hs χ polygon hcard)
      (strongPolygonLeftMiddleProfile hs χ polygon hcard) := by
    rw [Finset.disjoint_left]
    intro i hright hleft
    simp only [strongPolygonMiddleProfile, Finset.mem_filter,
      Finset.mem_univ, true_and] at hright hleft
    rw [hright] at hleft
    exact Turn.noConfusion hleft
  have hunion :
      strongPolygonRightMiddleProfile hs χ polygon hcard ∪
        strongPolygonLeftMiddleProfile hs χ polygon hcard = Finset.univ := by
    ext i
    simp only [strongPolygonMiddleProfile, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    cases strongPolygonEndpointMiddleColor hs χ polygon hcard i <;> simp
  rw [← Finset.card_union_of_disjoint hdisjoint, hunion,
    Finset.card_univ, Fintype.card_fin]

private theorem strongPolygonMiddleProfile_card_le
    {n s target : ℕ} (hs : 2 ≤ s) (htarget : 3 ≤ target)
    {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = s) (hstrong : IsStrongPolygonSet χ polygon)
    (c : Turn)
    (hno : if c = Turn.right then ¬ContainsCapSet χ polygon target
      else ¬ContainsCupSet χ polygon target) :
    (strongPolygonMiddleProfile hs χ polygon hcard c).card ≤ target - 3 := by
  by_contra hnot
  have hneeded : target - 2 ≤
      (strongPolygonMiddleProfile hs χ polygon hcard c).card := by
    omega
  obtain ⟨middle, hmiddleSub, hmiddleCard⟩ :=
    Finset.exists_subset_card_eq hneeded
  let support := pascalProfileEndpointSupport hs middle
  let e : Fin s ↪o Fin n := polygon.orderEmbOfFin hcard
  let mono := support.image e
  have hmonoSub : mono ⊆ polygon := by
    intro x hx
    simp only [mono, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact polygon.orderEmbOfFin_mem hcard i
  have hmonoCard : mono.card = target := by
    change (support.image e).card = target
    rw [Finset.card_image_of_injective _ e.injective]
    change (pascalProfileEndpointSupport hs middle).card = target
    rw [pascalProfileEndpointSupport_card hs middle, hmiddleCard]
    omega
  have hmonoColor : ∀ t : OrderedTriple n,
      t.i ∈ mono → t.j ∈ mono → t.k ∈ mono → χ t = c := by
    simpa only [mono, support, e] using
      (strongPolygon_endpointSupport_isColor hstrong c middle hmiddleSub)
  cases c with
  | left => exact hno ⟨mono, hmonoSub, hmonoCard, hmonoColor⟩
  | right => exact hno ⟨mono, hmonoSub, hmonoCard, hmonoColor⟩

/-- Frozen FP-03 contract: endpoint-middle colors partition all internal
positions, and the two forbidden monochromatic sizes bound the profile. -/
theorem StrongPolygonMiddleProfileInPascalWindow
    {n s a u : ℕ} {hs : 2 ≤ s} {ha : 3 ≤ a} {hu : 3 ≤ u}
    {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = s) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon a)
    (hnoCup : ¬ContainsCupSet χ polygon u) :
    (strongPolygonRightMiddleProfile hs χ polygon hcard).card +
          (strongPolygonLeftMiddleProfile hs χ polygon hcard).card = s - 2 ∧
      (strongPolygonRightMiddleProfile hs χ polygon hcard).card ≤ a - 3 ∧
      (strongPolygonLeftMiddleProfile hs χ polygon hcard).card ≤ u - 3 := by
  refine ⟨strongPolygonMiddleProfile_partition hs χ polygon hcard, ?_, ?_⟩
  · exact strongPolygonMiddleProfile_card_le hs ha hcard hstrong Turn.right
      (by simpa using hnoCap)
  · exact strongPolygonMiddleProfile_card_le hs hu hcard hstrong Turn.left
      (by simpa using hnoCup)

/-- At state `(5,5,6)`, exactly two of the four internal positions have each
color. -/
theorem strongSixMiddleProfile_556
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon 5)
    (hnoCup : ¬ContainsCupSet χ polygon 5) :
    (strongPolygonRightMiddleProfile (by omega : 2 ≤ 6)
        χ polygon hcard).card = 2 ∧
      (strongPolygonLeftMiddleProfile (by omega : 2 ≤ 6)
        χ polygon hcard).card = 2 := by
  have hwindow := StrongPolygonMiddleProfileInPascalWindow
    (hs := (by omega : 2 ≤ 6)) (ha := (by omega : 3 ≤ 5))
    (hu := (by omega : 3 ≤ 5)) hcard hstrong hnoCap hnoCup
  omega

/-- At state `(5,6,6)`, the right profile has size one or two and the left
profile has the complementary size two or three. -/
theorem strongSixMiddleProfile_567
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon 5)
    (hnoCup : ¬ContainsCupSet χ polygon 6) :
    (strongPolygonRightMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card +
        (strongPolygonLeftMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card = 4 ∧
      1 ≤ (strongPolygonRightMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ∧
      (strongPolygonRightMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ≤ 2 ∧
      2 ≤ (strongPolygonLeftMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ∧
      (strongPolygonLeftMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ≤ 3 := by
  have hwindow := StrongPolygonMiddleProfileInPascalWindow
    (hs := (by omega : 2 ≤ 6)) (ha := (by omega : 3 ≤ 5))
    (hu := (by omega : 3 ≤ 6)) hcard hstrong hnoCap hnoCup
  omega

/-- The color-dual state `(6,5,6)` has the reversed profile ranges. -/
theorem strongSixMiddleProfile_657
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon 6)
    (hnoCup : ¬ContainsCupSet χ polygon 5) :
    (strongPolygonRightMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card +
        (strongPolygonLeftMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card = 4 ∧
      2 ≤ (strongPolygonRightMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ∧
      (strongPolygonRightMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ≤ 3 ∧
      1 ≤ (strongPolygonLeftMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ∧
      (strongPolygonLeftMiddleProfile (by omega : 2 ≤ 6)
          χ polygon hcard).card ≤ 2 := by
  have hwindow := StrongPolygonMiddleProfileInPascalWindow
    (hs := (by omega : 2 ≤ 6)) (ha := (by omega : 3 ≤ 6))
    (hu := (by omega : 3 ≤ 5)) hcard hstrong hnoCap hnoCup
  omega

/-- The binomial capacity of the internal profiles allowed by the two local
monochromatic exclusions.  The summation index is the left-profile size. -/
def strongPolygonMiddleProfileCapacity (s a u : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc (s - a + 1) (u - 3), Nat.choose (s - 2) j

/-- The coefficient at the actual left-profile size is one term of the local
profile capacity. -/
theorem StrongPolygonMiddleProfileInPascalWindow.choose_left_le_capacity
    {n s a u : ℕ} {hs : 2 ≤ s} {ha : 3 ≤ a} {hu : 3 ≤ u}
    {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = s) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon a)
    (hnoCup : ¬ContainsCupSet χ polygon u) (haS : a ≤ s) :
    Nat.choose (s - 2)
        (strongPolygonLeftMiddleProfile hs χ polygon hcard).card ≤
      strongPolygonMiddleProfileCapacity s a u := by
  have hwindow := StrongPolygonMiddleProfileInPascalWindow
    (hs := hs) (ha := ha) (hu := hu) hcard hstrong hnoCap hnoCup
  unfold strongPolygonMiddleProfileCapacity
  apply Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
  simp only [Finset.mem_Icc]
  omega

/-- The local profile-capacity window embeds strictly inside the published
outer Pascal window; this is an arithmetic consumer, not a tail bound. -/
theorem strongPolygonMiddleProfileCapacity_le_decomposableBinomialWindow
    (s a u : ℕ) :
    strongPolygonMiddleProfileCapacity s a u ≤
      decomposableBinomialWindow a u s := by
  unfold strongPolygonMiddleProfileCapacity decomposableBinomialWindow
  apply Finset.sum_le_sum_of_subset
  intro j hj
  simp only [Finset.mem_Icc] at hj ⊢
  omega

/-- The actual profile coefficient is therefore absorbed by the published
binomial window, without invoking either one-sided Pascal-tail theorem. -/
theorem StrongPolygonMiddleProfileInPascalWindow.choose_left_le_binomialWindow
    {n s a u : ℕ} {hs : 2 ≤ s} {ha : 3 ≤ a} {hu : 3 ≤ u}
    {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = s) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon a)
    (hnoCup : ¬ContainsCupSet χ polygon u) (haS : a ≤ s) :
    Nat.choose (s - 2)
        (strongPolygonLeftMiddleProfile hs χ polygon hcard).card ≤
      decomposableBinomialWindow a u s :=
  (StrongPolygonMiddleProfileInPascalWindow.choose_left_le_capacity
    (hs := hs) (ha := ha) (hu := hu)
    hcard hstrong hnoCap hnoCup haS).trans
      (strongPolygonMiddleProfileCapacity_le_decomposableBinomialWindow s a u)

theorem strongPolygonMiddleProfileCapacity_556 :
    strongPolygonMiddleProfileCapacity 6 5 5 = 6 := by
  decide

theorem strongPolygonMiddleProfileCapacity_567 :
    strongPolygonMiddleProfileCapacity 6 5 6 = 10 := by
  decide

theorem strongPolygonMiddleProfileCapacity_657 :
    strongPolygonMiddleProfileCapacity 6 6 5 = 10 := by
  decide

/-- A fresh derivation of the existing state-567 middle-word theorem from the
generic profile bounds.  The proof uses only profile membership and cardinal
monotonicity; it does not invoke the earlier state-specific proof. -/
theorem strongSixMiddleWordWeightOneOrTwo_of_profile
    {n : ℕ} {χ : TripleColoring n} {polygon : Finset (Fin n)}
    (hcard : polygon.card = 6) (hstrong : IsStrongPolygonSet χ polygon)
    (hnoCap : ¬ContainsCapSet χ polygon 5)
    (hnoCup : ¬ContainsCupSet χ polygon 6) :
    StrongSixMiddleWordWeightOneOrTwo χ polygon hcard := by
  let hs6 : 2 ≤ 6 := by omega
  let right := strongPolygonRightMiddleProfile hs6 χ polygon hcard
  have hprofile := strongSixMiddleProfile_567 hcard hstrong hnoCap hnoCup
  have hrightPos : 0 < right.card := by
    simpa only [right, hs6] using hprofile.2.1
  have hrightLe : right.card ≤ 2 := by
    simpa only [right, hs6] using hprofile.2.2.1
  have hsomeColor :
      χ ⟨polygon.orderEmbOfFin hcard 0,
          polygon.orderEmbOfFin hcard 1,
          polygon.orderEmbOfFin hcard 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨polygon.orderEmbOfFin hcard 0,
          polygon.orderEmbOfFin hcard 2,
          polygon.orderEmbOfFin hcard 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨polygon.orderEmbOfFin hcard 0,
          polygon.orderEmbOfFin hcard 3,
          polygon.orderEmbOfFin hcard 5, by simp, by simp⟩ = Turn.right ∨
      χ ⟨polygon.orderEmbOfFin hcard 0,
          polygon.orderEmbOfFin hcard 4,
          polygon.orderEmbOfFin hcard 5, by simp, by simp⟩ = Turn.right := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hrightPos
    have hiColor := (Finset.mem_filter.mp hi).2
    fin_cases i
    · exact Or.inl (by
        simpa [right, hs6, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast] using hiColor)
    · exact Or.inr (Or.inl (by
        simpa [right, hs6, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast] using hiColor))
    · exact Or.inr (Or.inr (Or.inl (by
        simpa [right, hs6, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast] using hiColor)))
    · exact Or.inr (Or.inr (Or.inr (by
        simpa [right, hs6, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast] using hiColor)))
  unfold StrongSixMiddleWordWeightOneOrTwo
  dsimp only
  refine ⟨hsomeColor, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2, h3⟩
    have hsub : ({0, 1, 2} : Finset (Fin 4)) ⊆ right := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h1]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h2]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h3]
    have hthree := Finset.card_le_card hsub
    have hthreeCard : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by
      decide
    rw [hthreeCard] at hthree
    omega
  · rintro ⟨h1, h2, h4⟩
    have hsub : ({0, 1, 3} : Finset (Fin 4)) ⊆ right := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h1]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h2]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h4]
    have hthree := Finset.card_le_card hsub
    have hthreeCard : ({0, 1, 3} : Finset (Fin 4)).card = 3 := by
      decide
    rw [hthreeCard] at hthree
    omega
  · rintro ⟨h1, h3, h4⟩
    have hsub : ({0, 2, 3} : Finset (Fin 4)) ⊆ right := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h1]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h3]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h4]
    have hthree := Finset.card_le_card hsub
    have hthreeCard : ({0, 2, 3} : Finset (Fin 4)).card = 3 := by
      decide
    rw [hthreeCard] at hthree
    omega
  · rintro ⟨h2, h3, h4⟩
    have hsub : ({1, 2, 3} : Finset (Fin 4)) ⊆ right := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h2]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h3]
      · simp [right, strongPolygonMiddleProfile,
          strongPolygonEndpointMiddleColor, pascalProfileFirst,
          pascalProfileMiddle, pascalProfileLast, h4]
    have hthree := Finset.card_le_card hsub
    have hthreeCard : ({1, 2, 3} : Finset (Fin 4)).card = 3 := by
      decide
    rw [hthreeCard] at hthree
    omega

end

end ErdosSzekeres
