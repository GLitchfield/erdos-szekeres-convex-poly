module

public import ErdosSzekeres.HalfPureSingletonFanFin9
public import ErdosSzekeres.StructuralChargingPascalTailGates
public import ErdosSzekeres.StructuralChargingResidualProbeGeneric
public import ErdosSzekeres.StructuralChargingTransport

@[expose] public section

/-!
# Variable-carrier residual probes

The state-567 residual argument uses two six-point carriers.  This file
separates the finite-set escape mechanism from equality of the carrier
cardinalities and records the first genuinely adjacent specialization: at
state `(5,5,6)`, a strong five-set and one exterior singleton leave an
eight-point residual.

The resulting count is infrastructure, not a proof of the Pascal-tail bound.
The all-in-one terminal named below is deliberately only an interface: at this
exact cardinality it is equivalent to the desired finite two-side bound, since
the preceding declarations derive its extra probe and count hypotheses from
every counterexample.  Progress beyond this file therefore requires a genuine
collision-or-large-fiber color lemma, not merely a proof of that terminal.
-/

namespace ErdosSzekeres

/-- Generic finite-set extraction of a residual escape from two disjoint
carriers of possibly different cardinalities. -/
theorem pairResidualEscape_of_avoidsEveryDeletion_unequal
    {n firstCard secondCard residualCard blockCard witnessCard : ℕ}
    {χ : TripleColoring n} {ambient first second : Finset (Fin n)}
    (hambientCard :
      ambient.card = firstCard + secondCard + residualCard)
    (hfirstSub : first ⊆ ambient) (hsecondSub : second ⊆ ambient)
    (hdisjoint : Disjoint first second)
    (hfirstCard : first.card = firstCard)
    (hsecondCard : second.card = secondCard)
    (hpacking : StrongPolygonAvoidsEveryDeletion χ ambient
      (blockCard + 2) witnessCard) :
    PairResidualEscape χ ambient first second residualCard blockCard
      witnessCard := by
  have hpairSub : first ∪ second ⊆ ambient :=
    Finset.union_subset hfirstSub hsecondSub
  have hpairCard :
      (first ∪ second).card = firstCard + secondCard := by
    rw [Finset.card_union_of_disjoint hdisjoint, hfirstCard, hsecondCard]
  refine ⟨?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hpairSub, hambientCard, hpairCard]
    omega
  · intro a haFirst b hbSecond block hblockSub hblockCard
    have haAmbient : a ∈ ambient := hfirstSub haFirst
    have hbAmbient : b ∈ ambient := hsecondSub hbSecond
    have hblockAmbient : block ⊆ ambient :=
      hblockSub.trans Finset.sdiff_subset
    have hab : a ≠ b := by
      intro hab
      subst b
      exact Finset.disjoint_left.mp hdisjoint haFirst hbSecond
    have haBlock : a ∉ block := by
      intro ha
      exact (Finset.mem_sdiff.mp (hblockSub ha)).2
        (Finset.mem_union_left second haFirst)
    have hbBlock : b ∉ block := by
      intro hb
      exact (Finset.mem_sdiff.mp (hblockSub hb)).2
        (Finset.mem_union_right first hbSecond)
    apply hpacking (insert a (insert b block))
    · exact Finset.insert_subset haAmbient
        (Finset.insert_subset hbAmbient hblockAmbient)
    · simp [hab, haBlock, hbBlock, hblockCard]

/-- Hereditary transport of the kernel-checked Fin-9 strong-five theorem to
an arbitrary one-change support. -/
theorem containsStrongFive_of_oneChange_card_ge_nine
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (hone : OneChangeOn χ support) (hcard : 9 ≤ support.card) :
    ContainsStrongPolygonSet χ support 5 := by
  obtain ⟨sample, hsampleSub, hsampleCard⟩ :=
    Finset.exists_subset_card_eq hcard
  let e : Fin 9 ↪o Fin n := sample.orderEmbOfFin hsampleCard
  let ψ : TripleColoring 9 := χ.restrict e
  have heMem (i : Fin 9) : e i ∈ support :=
    hsampleSub (sample.orderEmbOfFin_mem hsampleCard i)
  have honeψ : OneChangeOn ψ Finset.univ := by
    intro a b c d hab hbc hcd _ _ _ _
    simpa [ψ, TripleColoring.restrict, OrderedTriple.map] using
      hone (e.strictMono hab) (e.strictMono hbc) (e.strictMono hcd)
        (heMem a) (heMem b) (heMem c) (heMem d)
  have hfinite := containsStrongFiveFinNine_of_oneChange ψ honeψ
  have hmapped := containsStrongPolygonSet_map_restrict e hfinite
  exact FinsetPolygon.ContainsStrongPolygonSet.mono hmapped (by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact heMem i)

theorem decomposableThreshold_555 : decomposableThreshold 5 5 5 = 8 := by
  norm_num [decomposableThreshold, decomposableBinomialWindow, Nat.choose,
    Finset.sum_Icc_succ_top]

theorem lowerPascalTailReservoir_556 :
    lowerPascalTailReservoir 5 5 6 = 14 := by
  norm_num [lowerPascalTailReservoir, decomposableThreshold,
    decomposableBinomialWindow, Nat.choose, Finset.sum_Icc_succ_top]

/-- The Fin-9 theorem is precisely the hereditary predecessor state needed
for five-point deletion packing. -/
theorem oneChangeStateUpper_555 : OneChangeStateUpper 5 5 5 := by
  intro n χ support hone hcard
  have hnine : 9 ≤ support.card := by
    rw [decomposableThreshold_555] at hcard
    omega
  exact Or.inr (Or.inr
    (containsStrongFive_of_oneChange_card_ge_nine hone hnine))

/-- At the `(5,5,6)` Pascal reservoir, a strong five carrier and a singleton
carrier leave an eight-point residual with three-block strong-five escapes. -/
def FiveSingletonResidualProbe556 {n : ℕ} (χ : TripleColoring n)
    (ambient first singleton : Finset (Fin n)) : Prop :=
  first ⊆ ambient ∧ singleton ⊆ ambient ∧ Disjoint first singleton ∧
    first.card = 5 ∧ singleton.card = 1 ∧
      IsStrongPolygonSet χ first ∧
        PairResidualEscape χ ambient first singleton 8 3 5

/-- Every target-free one-change set of cardinality fourteen produces the
five-plus-singleton residual probe system. -/
theorem exists_fiveSingletonResidualProbe556
    {n : ℕ} {χ : TripleColoring n} {ambient : Finset (Fin n)}
    (hone : OneChangeOn χ ambient) (hcard : ambient.card = 14)
    (hnoCap : ¬ContainsCapSet χ ambient 5)
    (hnoCup : ¬ContainsCupSet χ ambient 5) :
    ∃ first singleton,
      FiveSingletonResidualProbe556 χ ambient first singleton := by
  obtain ⟨first, hfirstSub, hfirstCard, hfirstStrong⟩ :=
    containsStrongFive_of_oneChange_card_ge_nine hone (by omega)
  have hcomplementCard : (ambient \ first).card = 9 := by
    rw [Finset.card_sdiff_of_subset hfirstSub, hcard, hfirstCard]
  have hcomplementNonempty : (ambient \ first).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨q, hqComplement⟩ := hcomplementNonempty
  let singleton : Finset (Fin n) := {q}
  have hsingletonSub : singleton ⊆ ambient := by
    intro x hx
    have hxq : x = q := by simpa [singleton] using hx
    subst x
    exact (Finset.mem_sdiff.mp hqComplement).1
  have hdisjoint : Disjoint first singleton := by
    rw [Finset.disjoint_left]
    intro x hxFirst hxSingleton
    have hxq : x = q := by simpa [singleton] using hxSingleton
    subst x
    exact (Finset.mem_sdiff.mp hqComplement).2 hxFirst
  have hsingletonCard : singleton.card = 1 := by simp [singleton]
  have hpacking : StrongPolygonAvoidsEveryDeletion χ ambient 5 5 := by
    apply strongPolygonAvoidsEveryDeletion_of_oneChangeStateUpper
      oneChangeStateUpper_555 hone
    · rw [decomposableThreshold_555, hcard]
    · exact hnoCap
    · exact hnoCup
  have hescape : PairResidualEscape χ ambient first singleton 8 3 5 := by
    apply pairResidualEscape_of_avoidsEveryDeletion_unequal
      (firstCard := 5) (secondCard := 1)
      (residualCard := 8) (blockCard := 3) (witnessCard := 5)
    · omega
    · exact hfirstSub
    · exact hsingletonSub
    · exact hdisjoint
    · exact hfirstCard
    · exact hsingletonCard
    · simpa using hpacking
  exact ⟨first, singleton, hfirstSub, hsingletonSub, hdisjoint,
    hfirstCard, hsingletonCard, hfirstStrong, hescape⟩

/-- The no-strong-six hypothesis forces at least ten bad residual
three-blocks in every eight-point residual. -/
theorem ten_le_card_badResidualBlocks_three_of_noStrongSix
    {n : ℕ} {χ : TripleColoring n} {residual : Finset (Fin n)}
    (hresidualCard : residual.card = 8)
    (hnoStrongSix : ¬ContainsStrongPolygonSet χ residual 6) :
    10 ≤ (BadResidualBlocks χ residual 3).card := by
  have hseedCover : ∀ seed ∈ residual.powersetCard (3 - 1),
      ∃ block ∈ BadResidualBlocks χ residual 3, seed ⊆ block := by
    intro seed hseed
    have hseedData := Finset.mem_powersetCard.mp hseed
    exact badResidualBlocks_cover_seed
      (R := 8) (W := 5) (B := 3)
      (by norm_num) (by norm_num) (by norm_num) hresidualCard
      hnoStrongSix hseedData.1 hseedData.2
  have hcount := choose_le_badResidualBlocks_card_mul
    (R := 8) (B := 3) (χ := χ) (residual := residual)
    (by norm_num) hresidualCard hseedCover
  norm_num [Nat.choose] at hcount ⊢
  omega

/-- Exact color-sensitive terminal left after the unequal-carrier producer and
the residual count.  This retains the ordered cap-four-free sides needed by
the Pascal-tail application.  It is a packaging boundary, not an independent
reduction: at total cardinality fourteen it is equivalent to the two-side
bound consumed below. -/
def FiveSingletonResidualProbeImpossible556 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right first singleton : Finset (Fin n)},
    Disjoint left right →
    (∀ x ∈ left, ∀ y ∈ right, x < y) →
    left.card + right.card = 14 →
    ¬ContainsCapSet χ left 4 →
    ¬ContainsCapSet χ right 4 →
    OneChangeOn χ (left ∪ right) →
    ¬ContainsCapSet χ (left ∪ right) 5 →
    ¬ContainsCupSet χ (left ∪ right) 5 →
    ¬ContainsStrongPolygonSet χ (left ∪ right) 6 →
    FiveSingletonResidualProbe556 χ (left ∪ right) first singleton →
    10 ≤ (BadResidualBlocks χ
      ((left ∪ right) \ (first ∪ singleton)) 3).card → False

/-- The variable-carrier terminal would close the adjacent `(5,5,6)`
Pascal-tail two-side bound.  The theorem makes the remaining obstruction
explicit and does not assume the desired bound. -/
theorem pascalTailTwoSideBound_556_of_fiveSingletonResidualProbeImpossible
    (hterminal : FiveSingletonResidualProbeImpossible556) :
    PascalTailTwoSideBound 5 5 6 := by
  intro n χ left right hdisjoint horder hleftCap hrightCap hone
    hnoCap hnoCup hnoStrong
  rw [lowerPascalTailReservoir_556]
  by_contra hnot
  have htotal : 14 ≤ left.card + right.card := by omega
  by_cases hleftLarge : 14 ≤ left.card
  · obtain ⟨left', hleftSub, hleftCard⟩ :=
      Finset.exists_subset_card_eq hleftLarge
    let right' : Finset (Fin n) := ∅
    have hrightSub : right' ⊆ right := by simp [right']
    have hdisjoint' : Disjoint left' right' := by simp [right']
    have horder' : ∀ x ∈ left', ∀ y ∈ right', x < y := by
      simp [right']
    have hunionSub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    have hambientCard : left'.card + right'.card = 14 := by
      simp [right', hleftCard]
    have hleftCap' : ¬ContainsCapSet χ left' 4 := by
      intro hcap
      exact hleftCap (FinsetPolygon.ContainsCapSet.mono hcap hleftSub)
    have hrightCap' : ¬ContainsCapSet χ right' 4 := by
      intro hcap
      exact hrightCap (FinsetPolygon.ContainsCapSet.mono hcap hrightSub)
    have hunionCard : (left' ∪ right').card = 14 := by
      rw [Finset.card_union_of_disjoint hdisjoint']
      exact hambientCard
    have hone' : OneChangeOn χ (left' ∪ right') :=
      hone.mono hunionSub
    have hnoCap' : ¬ContainsCapSet χ (left' ∪ right') 5 := by
      intro hcap
      exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub)
    have hnoCup' : ¬ContainsCupSet χ (left' ∪ right') 5 := by
      intro hcup
      exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub)
    have hnoStrong' :
        ¬ContainsStrongPolygonSet χ (left' ∪ right') 6 := by
      intro hstrong
      exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub)
    obtain ⟨first, singleton, hprobe⟩ :=
      exists_fiveSingletonResidualProbe556 hone' hunionCard
        hnoCap' hnoCup'
    have hresidualNoStrong : ¬ContainsStrongPolygonSet χ
        ((left' ∪ right') \ (first ∪ singleton)) 6 := by
      intro hstrong
      exact hnoStrong'
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
          Finset.sdiff_subset)
    exact hterminal hdisjoint' horder' hambientCard hleftCap'
      hrightCap' hone' hnoCap' hnoCup' hnoStrong' hprobe
      (ten_le_card_badResidualBlocks_three_of_noStrongSix
        hprobe.2.2.2.2.2.2.1 hresidualNoStrong)
  · have hleftSmall : left.card < 14 := by omega
    have hrightNeed : 14 - left.card ≤ right.card := by omega
    obtain ⟨right', hrightSub, hrightCard⟩ :=
      Finset.exists_subset_card_eq hrightNeed
    let left' := left
    have hleftSub : left' ⊆ left := by simp [left']
    have hdisjoint' : Disjoint left' right' :=
      hdisjoint.mono hleftSub hrightSub
    have horder' : ∀ x ∈ left', ∀ y ∈ right', x < y := by
      intro x hx y hy
      exact horder x (hleftSub hx) y (hrightSub hy)
    have hunionSub : left' ∪ right' ⊆ left ∪ right :=
      Finset.union_subset_union hleftSub hrightSub
    have hambientCard : left'.card + right'.card = 14 := by
      simp only [left', hrightCard]
      omega
    have hleftCap' : ¬ContainsCapSet χ left' 4 := by
      intro hcap
      exact hleftCap (FinsetPolygon.ContainsCapSet.mono hcap hleftSub)
    have hrightCap' : ¬ContainsCapSet χ right' 4 := by
      intro hcap
      exact hrightCap (FinsetPolygon.ContainsCapSet.mono hcap hrightSub)
    have hunionCard : (left' ∪ right').card = 14 := by
      rw [Finset.card_union_of_disjoint hdisjoint']
      exact hambientCard
    have hone' : OneChangeOn χ (left' ∪ right') :=
      hone.mono hunionSub
    have hnoCap' : ¬ContainsCapSet χ (left' ∪ right') 5 := by
      intro hcap
      exact hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hunionSub)
    have hnoCup' : ¬ContainsCupSet χ (left' ∪ right') 5 := by
      intro hcup
      exact hnoCup (FinsetPolygon.ContainsCupSet.mono hcup hunionSub)
    have hnoStrong' :
        ¬ContainsStrongPolygonSet χ (left' ∪ right') 6 := by
      intro hstrong
      exact hnoStrong
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong hunionSub)
    obtain ⟨first, singleton, hprobe⟩ :=
      exists_fiveSingletonResidualProbe556 hone' hunionCard
        hnoCap' hnoCup'
    have hresidualNoStrong : ¬ContainsStrongPolygonSet χ
        ((left' ∪ right') \ (first ∪ singleton)) 6 := by
      intro hstrong
      exact hnoStrong'
        (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong
          Finset.sdiff_subset)
    exact hterminal hdisjoint' horder' hambientCard hleftCap'
      hrightCap' hone' hnoCap' hnoCup' hnoStrong' hprobe
      (ten_le_card_badResidualBlocks_three_of_noStrongSix
        hprobe.2.2.2.2.2.2.1 hresidualNoStrong)

end ErdosSzekeres

end
