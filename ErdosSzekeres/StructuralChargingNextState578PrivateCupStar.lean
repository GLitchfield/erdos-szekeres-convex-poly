module

public import ErdosSzekeres.StructuralChargingNextState578SevenWitness

@[expose] public section

/-!
# The private-cup star at the state-578 gate

A minimum four-cup transversal inside the twelve vertices of three disjoint
four-cups has at least ten owners.  Consequently one selected cup consists
entirely of owners.  This file packages that cup and its four private cups as
a tree-ready star, then retains the six disjoint four-caps from the same exact
state.
-/

namespace ErdosSzekeres

/-- If at least ten of the twelve vertices in three disjoint four-cups are
selected, one of the cups is selected in full. -/
theorem ThreeDisjointCupCapFourPacking578.exists_cup_subset_of_ten_le
    {n : ℕ} {χ : TripleColoring n} {support transversal : Finset (Fin n)}
    (packing : ThreeDisjointCupCapFourPacking578 χ support)
    (hsub : transversal ⊆ packing.cupSupport)
    (hten : 10 ≤ transversal.card) :
    packing.cup₁ ⊆ transversal ∨
      packing.cup₂ ⊆ transversal ∨
      packing.cup₃ ⊆ transversal := by
  by_contra hfull
  simp only [not_or] at hfull
  obtain ⟨x₁, hx₁Cup, hx₁Not⟩ := Finset.not_subset.mp hfull.1
  obtain ⟨x₂, hx₂Cup, hx₂Not⟩ := Finset.not_subset.mp hfull.2.1
  obtain ⟨x₃, hx₃Cup, hx₃Not⟩ := Finset.not_subset.mp hfull.2.2
  have hx₁₂ : x₁ ≠ x₂ := by
    intro heq
    subst x₂
    exact (Finset.disjoint_left.mp packing.cup₁_cup₂) hx₁Cup hx₂Cup
  have hx₁₃ : x₁ ≠ x₃ := by
    intro heq
    subst x₃
    exact (Finset.disjoint_left.mp packing.cup₁_cup₃) hx₁Cup hx₃Cup
  have hx₂₃ : x₂ ≠ x₃ := by
    intro heq
    subst x₃
    exact (Finset.disjoint_left.mp packing.cup₂_cup₃) hx₂Cup hx₃Cup
  have hmissingCard : ({x₁, x₂, x₃} : Finset (Fin n)).card = 3 := by
    simp [hx₁₂, hx₁₃, hx₂₃]
  have hmissingSub : ({x₁, x₂, x₃} : Finset (Fin n)) ⊆
      packing.cupSupport \ transversal := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨by simp [ThreeDisjointCupCapFourPacking578.cupSupport, hx₁Cup], hx₁Not⟩
    · exact Finset.mem_sdiff.mpr
        ⟨by simp [ThreeDisjointCupCapFourPacking578.cupSupport, hx₂Cup], hx₂Not⟩
    · exact Finset.mem_sdiff.mpr
        ⟨by simp [ThreeDisjointCupCapFourPacking578.cupSupport, hx₃Cup], hx₃Not⟩
  have hcomplementCard : (packing.cupSupport \ transversal).card ≤ 2 := by
    rw [Finset.card_sdiff_of_subset hsub, packing.cupSupport_card]
    omega
  have hle := Finset.card_le_card hmissingSub
  omega

/-- On seven vertices, orientation eliminates the complete four-uniform
incidence obstruction: either there is a five-cup, or three vertices meet
every four-cup. -/
theorem sevenVertex_fourCupFamily_has_threeTransversal_or_cupFive
    {n : ℕ} {χ : TripleColoring n} {carrier : Finset (Fin n)}
    (hcard : carrier.card = 7) :
    ContainsCupSet χ carrier 5 ∨
      ∃ transversal : Finset (Fin n),
        transversal ⊆ carrier ∧
        transversal.card ≤ 3 ∧
        IsCupWitnessTransversal578 χ carrier transversal 4 := by
  by_cases hcupFive : ContainsCupSet χ carrier 5
  · exact Or.inl hcupFive
  right
  by_contra hnoTransversal
  have hallFour (four : Finset (Fin n))
      (hfourSub : four ⊆ carrier) (hfourCard : four.card = 4) :
      IsCupSet χ four := by
    let complement := carrier \ four
    have hcomplementSub : complement ⊆ carrier := Finset.sdiff_subset
    have hcomplementCard : complement.card = 3 := by
      rw [Finset.card_sdiff_of_subset hfourSub, hcard, hfourCard]
    have hnotTransversal :
        ¬IsCupWitnessTransversal578 χ carrier complement 4 := by
      intro htransversal
      exact hnoTransversal ⟨complement, hcomplementSub,
        by omega, htransversal⟩
    have hnotHit : ¬∀ cup, cup ∈ capWitnesses χ.dual carrier 4 →
        ¬Disjoint cup complement := by
      intro hhits
      exact hnotTransversal ⟨hcomplementSub, hhits⟩
    push Not at hnotHit
    obtain ⟨cup, hcup, hdisjoint⟩ := hnotHit
    have hcupData := mem_capWitnesses.mp hcup
    have hcupSubFour : cup ⊆ four := by
      intro x hxCup
      by_contra hxFour
      have hxComplement : x ∈ complement :=
        Finset.mem_sdiff.mpr ⟨hcupData.1 hxCup, hxFour⟩
      exact (Finset.disjoint_left.mp hdisjoint) hxCup hxComplement
    have hcupEq : cup = four := by
      apply (Finset.subset_iff_eq_of_card_le ?_).mp hcupSubFour
      rw [hfourCard, hcupData.2.1]
    have hcupSet : IsCupSet χ cup :=
      isCapSet_dual_iff.mp hcupData.2.2
    simpa [hcupEq] using hcupSet
  have hcarrierCup : IsCupSet χ carrier := by
    intro t hi hj hk
    let tripleSet : Finset (Fin n) := {t.i, t.j, t.k}
    have htripleSub : tripleSet ⊆ carrier := by
      intro x hx
      simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    have htripleCard : tripleSet.card = 3 := by
      simp [tripleSet, ne_of_lt t.hij, ne_of_lt t.hjk,
        ne_of_lt (t.hij.trans t.hjk)]
    have hrestCard : (carrier \ tripleSet).card = 4 := by
      rw [Finset.card_sdiff_of_subset htripleSub, hcard, htripleCard]
    obtain ⟨x, hxRest⟩ : (carrier \ tripleSet).Nonempty :=
      Finset.card_pos.mp (by rw [hrestCard]; omega)
    have hxCarrier : x ∈ carrier := (Finset.mem_sdiff.mp hxRest).1
    have hxTriple : x ∉ tripleSet := (Finset.mem_sdiff.mp hxRest).2
    let four := insert x tripleSet
    have hfourSub : four ⊆ carrier :=
      Finset.insert_subset hxCarrier htripleSub
    have hfourCard : four.card = 4 := by
      change (insert x tripleSet).card = 4
      rw [Finset.card_insert_of_notMem hxTriple, htripleCard]
    have hfourCup := hallFour four hfourSub hfourCard
    exact hfourCup t (by simp [four, tripleSet])
      (by simp [four, tripleSet]) (by simp [four, tripleSet])
  obtain ⟨five, hfiveSub, hfiveCard⟩ :=
    Finset.exists_subset_card_eq (show 5 ≤ carrier.card by omega)
  exact hcupFive ⟨five, hfiveSub, hfiveCard,
    FinsetPolygon.IsCupSet.mono hcarrierCup hfiveSub⟩

/-- The private tail of an owner is its chosen private four-cup with the owner
removed. -/
def PrivateCupLedger578.tailFor
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    (x : Fin n) (hx : x ∈ ledger.transversal) : Finset (Fin n) :=
  (ledger.cupFor x hx).erase x

/-- Every owner belongs to its chosen private cup. -/
theorem PrivateCupLedger578.owner_mem_cupFor
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    (x : Fin n) (hx : x ∈ ledger.transversal) :
    x ∈ ledger.cupFor x hx := by
  have hxInter : x ∈ ledger.transversal ∩ ledger.cupFor x hx := by
    rw [ledger.cupFor_private x hx]
    simp
  exact (Finset.mem_inter.mp hxInter).2

/-- A private tail has exactly three vertices. -/
theorem PrivateCupLedger578.tailFor_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    (x : Fin n) (hx : x ∈ ledger.transversal) :
    (ledger.tailFor x hx).card = 3 := by
  rw [PrivateCupLedger578.tailFor,
    Finset.card_erase_of_mem (ledger.owner_mem_cupFor x hx),
    (mem_capWitnesses.mp (ledger.cupFor_mem x hx)).2.1]

/-- The private cup is reconstructed by adjoining its owner to its tail. -/
theorem PrivateCupLedger578.insert_tailFor
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    (x : Fin n) (hx : x ∈ ledger.transversal) :
    insert x (ledger.tailFor x hx) = ledger.cupFor x hx := by
  exact Finset.insert_erase (ledger.owner_mem_cupFor x hx)

/-- Every private tail lies in the reservoir but outside the transversal. -/
theorem PrivateCupLedger578.tailFor_subset_sdiff
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    (x : Fin n) (hx : x ∈ ledger.transversal) :
    ledger.tailFor x hx ⊆ support \ ledger.transversal := by
  intro y hyTail
  have hyNe : y ≠ x := (Finset.mem_erase.mp hyTail).1
  have hyCup : y ∈ ledger.cupFor x hx := (Finset.mem_erase.mp hyTail).2
  refine Finset.mem_sdiff.mpr
    ⟨(mem_capWitnesses.mp (ledger.cupFor_mem x hx)).1 hyCup, ?_⟩
  intro hyTransversal
  have hyPrivate : y ∈ ({x} : Finset (Fin n)) := by
    rw [← ledger.cupFor_private x hx]
    exact Finset.mem_inter.mpr ⟨hyTransversal, hyCup⟩
  exact hyNe (Finset.mem_singleton.mp hyPrivate)

/-- Each private tail still has a vertex outside the original twelve selected
cup vertices. -/
theorem PrivateCupLedger578.tailFor_has_outside_cupSupport
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    (x : Fin n) (hx : x ∈ ledger.transversal) :
    (ledger.tailFor x hx \ state.packing.cupSupport).Nonempty := by
  obtain ⟨y, hy⟩ := ledger.cupFor_outside x hx
  have hyCup : y ∈ ledger.cupFor x hx := (Finset.mem_sdiff.mp hy).1
  have hyOutside : y ∉ state.packing.cupSupport := (Finset.mem_sdiff.mp hy).2
  have hyNe : y ≠ x := by
    intro heq
    subst y
    exact hyOutside (ledger.transversal_sub hx)
  exact ⟨y, Finset.mem_sdiff.mpr
    ⟨Finset.mem_erase.mpr ⟨hyNe, hyCup⟩, hyOutside⟩⟩

/-- Four owners lying on one selected four-cup, together with their private
four-cups. -/
structure PrivateCupStar578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state) where
  spine : Finset (Fin n)
  spine_selected :
    spine = state.packing.cup₁ ∨
      spine = state.packing.cup₂ ∨
      spine = state.packing.cup₃
  spine_sub_transversal : spine ⊆ ledger.transversal

/-- The owner pigeonhole produces a private-cup star. -/
theorem PrivateCupLedger578.exists_privateCupStar
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state) :
    Nonempty (PrivateCupStar578 ledger) := by
  rcases state.packing.exists_cup_subset_of_ten_le
      ledger.transversal_sub ledger.ten_le with h₁ | h₂ | h₃
  · exact ⟨{
      spine := state.packing.cup₁
      spine_selected := Or.inl rfl
      spine_sub_transversal := h₁
    }⟩
  · exact ⟨{
      spine := state.packing.cup₂
      spine_selected := Or.inr (Or.inl rfl)
      spine_sub_transversal := h₂
    }⟩
  · exact ⟨{
      spine := state.packing.cup₃
      spine_selected := Or.inr (Or.inr rfl)
      spine_sub_transversal := h₃
    }⟩

/-- The spine is one of the selected four-cup witnesses. -/
theorem PrivateCupStar578.spine_mem
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger) :
    star.spine ∈ capWitnesses χ.dual support 4 := by
  rcases star.spine_selected with h | h | h
  · simpa [h] using state.packing.cup₁_mem
  · simpa [h] using state.packing.cup₂_mem
  · simpa [h] using state.packing.cup₃_mem

/-- The spine has four vertices. -/
theorem PrivateCupStar578.spine_card
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger) : star.spine.card = 4 := by
  exact (mem_capWitnesses.mp star.spine_mem).2.1

/-- A spoke meets the owner spine exactly at its owner. -/
theorem PrivateCupStar578.spine_inter_cupFor
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger)
    {x : Fin n} (hx : x ∈ star.spine) :
    star.spine ∩ ledger.cupFor x (star.spine_sub_transversal hx) = {x} := by
  let hxTransversal := star.spine_sub_transversal hx
  apply Finset.ext
  intro y
  constructor
  · intro hy
    have hyPrivate : y ∈ ({x} : Finset (Fin n)) := by
      rw [← ledger.cupFor_private x hxTransversal]
      exact Finset.mem_inter.mpr
        ⟨star.spine_sub_transversal (Finset.mem_inter.mp hy).1,
          (Finset.mem_inter.mp hy).2⟩
    exact hyPrivate
  · intro hy
    have hyEq : y = x := Finset.mem_singleton.mp hy
    subst y
    exact Finset.mem_inter.mpr
      ⟨hx, ledger.owner_mem_cupFor x hxTransversal⟩

/-- Distinct spine owners have distinct private cups. -/
theorem PrivateCupStar578.cupFor_ne_of_owner_ne
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger)
    {x y : Fin n} (hx : x ∈ star.spine) (hy : y ∈ star.spine)
    (hxy : x ≠ y) :
    ledger.cupFor x (star.spine_sub_transversal hx) ≠
      ledger.cupFor y (star.spine_sub_transversal hy) := by
  intro heq
  exact hxy (ledger.cupFor_injective
    (star.spine_sub_transversal hx) (star.spine_sub_transversal hy) heq)

/-- A state-indexed strengthening of six-cap saturation.  The equality keeps
the regenerated state available to dependent private-cup data. -/
theorem SevenWitnessRegenerationPacking578.exists_sixCapSaturation_with_state
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (state : SevenWitnessRegenerationPacking578 χ reservoir)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    ∃ saturation : SixCapSaturation578 χ reservoir,
      saturation.state = state := by
  let rest₁ := reservoir \ state.fourCapSupport
  have hrest₁Card : rest₁.card = 16 := by
    rw [Finset.card_sdiff_of_subset state.fourCapSupport_subset,
      hcard, state.fourCapSupport_card]
  have hrest₁Decomposable : IsDecomposableOn χ rest₁ :=
    hreservoir.subset Finset.sdiff_subset (Finset.card_pos.mp (by omega))
  obtain ⟨cap₅, hcap₅Rest₁, hcap₅Card, hcap₅⟩ :=
    containsCapFour_of_predecessor_458 h458 hrest₁Decomposable
      (by omega) Finset.sdiff_subset hnoCup hnoStrong
  have hcap₅Support : cap₅ ⊆ reservoir :=
    hcap₅Rest₁.trans Finset.sdiff_subset
  let rest₂ := rest₁ \ cap₅
  have hrest₂Card : rest₂.card = 12 := by
    rw [Finset.card_sdiff_of_subset hcap₅Rest₁, hrest₁Card, hcap₅Card]
  have hrest₂Decomposable : IsDecomposableOn χ rest₂ :=
    hrest₁Decomposable.subset Finset.sdiff_subset
      (Finset.card_pos.mp (by omega))
  obtain ⟨cap₆, hcap₆Rest₂, hcap₆Card, hcap₆⟩ :=
    containsCapFour_of_predecessor_458 h458 hrest₂Decomposable
      (by omega) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      hnoCup hnoStrong
  have hcap₆Rest₁ : cap₆ ⊆ rest₁ :=
    hcap₆Rest₂.trans Finset.sdiff_subset
  have hcap₆Support : cap₆ ⊆ reservoir :=
    hcap₆Rest₁.trans Finset.sdiff_subset
  have hcap₅Four : Disjoint cap₅ state.fourCapSupport := by
    rw [Finset.disjoint_left]
    intro x hxCap₅ hxFour
    exact (Finset.mem_sdiff.mp (hcap₅Rest₁ hxCap₅)).2 hxFour
  have hcap₆Four : Disjoint cap₆ state.fourCapSupport := by
    rw [Finset.disjoint_left]
    intro x hxCap₆ hxFour
    exact (Finset.mem_sdiff.mp (hcap₆Rest₁ hxCap₆)).2 hxFour
  have hcap₅Cap₆ : Disjoint cap₅ cap₆ := by
    rw [Finset.disjoint_left]
    intro x hxCap₅ hxCap₆
    exact (Finset.mem_sdiff.mp (hcap₆Rest₂ hxCap₆)).2 hxCap₅
  exact ⟨{
    state := state
    cap₅ := cap₅
    cap₆ := cap₆
    cap₅_mem := mem_capWitnesses.mpr ⟨hcap₅Support, hcap₅Card, hcap₅⟩
    cap₆_mem := mem_capWitnesses.mpr ⟨hcap₆Support, hcap₆Card, hcap₆⟩
    cap₅_fourCapSupport := hcap₅Four
    cap₆_fourCapSupport := hcap₆Four
    cap₅_cap₆ := hcap₅Cap₆
  }, rfl⟩

/-- The private-cup star and the six disjoint cap blocks, chosen from the same
regenerated state. -/
structure PrivateCupStarSixCapState578
    {n : ℕ} (χ : TripleColoring n) (support : Finset (Fin n)) where
  saturation : SixCapSaturation578 χ support
  ledger : PrivateCupLedger578 saturation.state
  star : PrivateCupStar578 ledger

/-- The six saturated cap blocks as a finite indexed family. -/
def SixCapSaturation578.capAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) :
    Fin 6 → Finset (Fin n) :=
  ![saturation.state.regenerated,
    saturation.state.packing.cap₁,
    saturation.state.packing.cap₂,
    saturation.state.packing.cap₃,
    saturation.cap₅,
    saturation.cap₆]

/-- Every indexed saturated block is a four-cap witness. -/
theorem SixCapSaturation578.capAt_mem
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (saturation : SixCapSaturation578 χ support) (i : Fin 6) :
    saturation.capAt i ∈ capWitnesses χ support 4 := by
  fin_cases i <;> simp [SixCapSaturation578.capAt,
    saturation.state.regenerated_mem,
    saturation.state.packing.cap₁_mem,
    saturation.state.packing.cap₂_mem,
    saturation.state.packing.cap₃_mem,
    saturation.cap₅_mem, saturation.cap₆_mem]

/-- The four spine owners in sweep order. -/
def PrivateCupStar578.ownerAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger) : Fin 4 ↪o Fin n :=
  star.spine.orderEmbOfFin star.spine_card

theorem PrivateCupStar578.ownerAt_mem
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger) (i : Fin 4) :
    star.ownerAt i ∈ star.spine :=
  star.spine.orderEmbOfFin_mem star.spine_card i

/-- The private cup indexed by a spine position. -/
def PrivateCupStar578.privateCupAt
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger) (i : Fin 4) : Finset (Fin n) :=
  ledger.cupFor (star.ownerAt i)
    (star.spine_sub_transversal (star.ownerAt_mem i))

theorem PrivateCupStar578.privateCupAt_mem
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    {ledger : PrivateCupLedger578 state}
    (star : PrivateCupStar578 ledger) (i : Fin 4) :
    star.privateCupAt i ∈ capWitnesses χ.dual support 4 := by
  exact ledger.cupFor_mem _ _

/-- The first-joint-split constructor does not require the cup and cap to be
disjoint.  Four vertices in either witness already make their union large
enough to have a separating node. -/
theorem exists_cupCapFirstJointSplit578_general
    {n : ℕ} {χ : TripleColoring n} {support cup cap : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    (hcup : cup ∈ capWitnesses χ.dual support 4)
    (hcap : cap ∈ capWitnesses χ support 4) :
    Nonempty (CupCapFirstJointSplit578 tree cup cap) := by
  have hcupData := mem_capWitnesses.mp hcup
  have hcapData := mem_capWitnesses.mp hcap
  have hunionSub : cup ∪ cap ⊆ support :=
    Finset.union_subset hcupData.1 hcapData.1
  have hunionCard : 2 ≤ (cup ∪ cap).card := by
    have hle := Finset.card_le_card
      (Finset.subset_union_left : cup ⊆ cup ∪ cap)
    rw [hcupData.2.1] at hle
    omega
  let path := tree.lowestSeparatingPath hunionSub hunionCard
  obtain ⟨node, hlookup, hlocal, hnotLower, hnotUpper⟩ :=
    tree.lowestSeparatingPath_spec hunionSub hunionCard
  exact ⟨{
    path := path
    node := node
    lookup := hlookup
    allocated := tree.lowestSeparatingPath_isLowest hunionSub hunionCard
    union_local := hlocal
    not_all_lower := hnotLower
    not_all_upper := hnotUpper
  }⟩

/-- Enlarging a witness can only move its lowest separating address upward:
the larger witness's address is a prefix of the smaller witness's address. -/
theorem DecompositionTree.lowestSeparatingPath_prefix_of_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support)
    {small big : Finset (Fin n)}
    (hsmallSub : small ⊆ support) (hbigSub : big ⊆ support)
    (hsmallCard : 2 ≤ small.card) (hbigCard : 2 ≤ big.card)
    (hsmallBig : small ⊆ big) :
    tree.lowestSeparatingPath hbigSub hbigCard <+:
      tree.lowestSeparatingPath hsmallSub hsmallCard := by
  classical
  induction tree generalizing small big with
  | singleton i =>
      have hbigLe := Finset.card_le_card hbigSub
      simp at hbigLe
      omega
  | @split lower upper lowerTree upperTree deep ihLower ihUpper =>
      by_cases hbigLower : big ⊆ lower
      · have hsmallLower : small ⊆ lower := hsmallBig.trans hbigLower
        simp only [lowestSeparatingPath, hbigLower, hsmallLower,
          ↓reduceDIte]
        apply List.cons_prefix_cons.mpr
        exact ⟨rfl,
          ihLower hsmallLower hbigLower hsmallCard hbigCard hsmallBig⟩
      by_cases hbigUpper : big ⊆ upper
      · have hsmallUpper : small ⊆ upper := hsmallBig.trans hbigUpper
        have hsmallNotLower : ¬small ⊆ lower := by
          intro hsmallLower
          obtain ⟨x, hxSmall⟩ :=
            Finset.card_pos.mp (show 0 < small.card by omega)
          exact (Finset.disjoint_left.mp deep.disjoint)
            (hsmallLower hxSmall) (hsmallUpper hxSmall)
        simp only [lowestSeparatingPath, hbigLower, hbigUpper,
          hsmallNotLower, hsmallUpper, ↓reduceDIte]
        apply List.cons_prefix_cons.mpr
        exact ⟨rfl,
          ihUpper hsmallUpper hbigUpper hsmallCard hbigCard hsmallBig⟩
      · simp [lowestSeparatingPath, hbigLower, hbigUpper]

/-- The mixed `4 × 6` address ledger between the private-cup star and the six
cap blocks.  Cells allow intersection; no disjointness or common-address
assumption is built into the structure. -/
structure PrivateCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (tree : DecompositionTree χ support) where
  cell : ∀ i : Fin 4, ∀ j : Fin 6,
    CupCapFirstJointSplit578 tree
      (joint.star.privateCupAt i) (joint.saturation.capAt j)

/-- Every joint private-star/six-cap state has its full mixed address matrix
inside any explicit decomposition tree of the support. -/
theorem exists_privateCupSixCapAddressMatrix578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support)
    (tree : DecompositionTree χ support) :
    Nonempty (PrivateCupSixCapAddressMatrix578 joint tree) := by
  classical
  exact ⟨{
    cell := fun i j ↦ Classical.choice
      (exists_cupCapFirstJointSplit578_general tree
        (joint.star.privateCupAt_mem i) (joint.saturation.capAt_mem j))
  }⟩

/-- In each owner row, all six joint addresses are prefixes of the private
cup's own separating address. -/
theorem PrivateCupSixCapAddressMatrix578.exists_row_common_extension
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : PrivateCupSixCapAddressMatrix578 joint tree)
    (i : Fin 4) :
    ∃ path : List Bool, ∀ j : Fin 6, (matrix.cell i j).path <+: path := by
  let cup := joint.star.privateCupAt i
  have hcupData := mem_capWitnesses.mp (joint.star.privateCupAt_mem i)
  have hcupCard : 2 ≤ cup.card := by rw [hcupData.2.1]; omega
  let cupPath := tree.lowestSeparatingPath hcupData.1 hcupCard
  refine ⟨cupPath, ?_⟩
  intro j
  let cap := joint.saturation.capAt j
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem j)
  have hunionSub : cup ∪ cap ⊆ support :=
    Finset.union_subset hcupData.1 hcapData.1
  have hunionCard : 2 ≤ (cup ∪ cap).card := by
    have hle := Finset.card_le_card
      (Finset.subset_union_left : cup ⊆ cup ∪ cap)
    rw [hcupData.2.1] at hle
    omega
  have hprefix := tree.lowestSeparatingPath_prefix_of_subset
    hcupData.1 hunionSub hcupCard hunionCard
    (Finset.subset_union_left : cup ⊆ cup ∪ cap)
  have hpathEq := (matrix.cell i j).allocated.eq_lowestSeparatingPath
    hunionSub hunionCard
  rw [hpathEq]
  exact hprefix

/-- Any two joint addresses in one owner row are prefix-comparable. -/
theorem PrivateCupSixCapAddressMatrix578.row_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : PrivateCupSixCapAddressMatrix578 joint tree)
    (i : Fin 4) (j k : Fin 6) :
    (matrix.cell i j).path <+: (matrix.cell i k).path ∨
      (matrix.cell i k).path <+: (matrix.cell i j).path := by
  obtain ⟨path, hprefix⟩ := matrix.exists_row_common_extension i
  exact List.prefix_or_prefix_of_prefix (hprefix j) (hprefix k)

/-- The same prefix-chain law holds down each cap column. -/
theorem PrivateCupSixCapAddressMatrix578.column_paths_comparable
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    {tree : DecompositionTree χ support}
    (matrix : PrivateCupSixCapAddressMatrix578 joint tree)
    (i k : Fin 4) (j : Fin 6) :
    (matrix.cell i j).path <+: (matrix.cell k j).path ∨
      (matrix.cell k j).path <+: (matrix.cell i j).path := by
  let cap := joint.saturation.capAt j
  have hcapData := mem_capWitnesses.mp (joint.saturation.capAt_mem j)
  have hcapCard : 2 ≤ cap.card := by rw [hcapData.2.1]; omega
  let capPath := tree.lowestSeparatingPath hcapData.1 hcapCard
  have hprefix (owner : Fin 4) : (matrix.cell owner j).path <+: capPath := by
    let cup := joint.star.privateCupAt owner
    have hcupData := mem_capWitnesses.mp (joint.star.privateCupAt_mem owner)
    have hunionSub : cup ∪ cap ⊆ support :=
      Finset.union_subset hcupData.1 hcapData.1
    have hunionCard : 2 ≤ (cup ∪ cap).card := by
      have hle := Finset.card_le_card
        (Finset.subset_union_right : cap ⊆ cup ∪ cap)
      rw [hcapData.2.1] at hle
      omega
    have hp := tree.lowestSeparatingPath_prefix_of_subset
      hcapData.1 hunionSub hcapCard hunionCard
      (Finset.subset_union_right : cap ⊆ cup ∪ cap)
    have hpathEq := (matrix.cell owner j).allocated.eq_lowestSeparatingPath
      hunionSub hunionCard
    rw [hpathEq]
    exact hp
  exact List.prefix_or_prefix_of_prefix (hprefix i) (hprefix k)

/-- Reconnect the private-star/six-cap joint state to the exact 32-vertex
singleton-root gate. -/
theorem exists_fourthDisjointCup_or_privateCupStarSixCapState_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    (∃ state : SevenWitnessRegenerationPacking578 χ reservoir,
      ∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
        Disjoint cup state.packing.cupSupport) ∨
      Nonempty (PrivateCupStarSixCapState578 χ reservoir) := by
  obtain ⟨state, hbranch⟩ :=
    exists_sevenWitness_with_fourthDisjointCup_or_privateCupLedger_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong
  rcases hbranch with hfourth | hledger
  · left
    obtain ⟨cup, hcup, hdisjoint⟩ := hfourth
    exact ⟨state, cup, hcup, hdisjoint⟩
  · right
    obtain ⟨ledger⟩ := hledger
    obtain ⟨saturation, hsaturation⟩ :=
      state.exists_sixCapSaturation_with_state
        h458 hreservoir hcard hnoCup hnoStrong
    have ledger' : PrivateCupLedger578 saturation.state := by
      rw [hsaturation]
      exact ledger
    obtain ⟨star⟩ := ledger'.exists_privateCupStar
    exact ⟨{
      saturation := saturation
      ledger := ledger'
      star := star
    }⟩

/-- The exact gate now exposes the provider-vetted mixed `4 × 6` matrix and
its prefix-chain structure, unless the fourth disjoint cup branch occurs. -/
theorem exists_fourthDisjointCup_or_privateCupSixCapAddressMatrix_at_32
    (h458 : DecomposableStateUpper 4 5 8)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    (hreservoir : IsDecomposableOn χ reservoir)
    (hroot : HasDeepBelowSplit χ {q} reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ reservoir) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    (∃ state : SevenWitnessRegenerationPacking578 χ reservoir,
      ∃ cup, cup ∈ capWitnesses χ.dual reservoir 4 ∧
        Disjoint cup state.packing.cupSupport) ∨
      ∃ joint : PrivateCupStarSixCapState578 χ reservoir,
        ∃ tree : DecompositionTree χ reservoir,
          Nonempty (PrivateCupSixCapAddressMatrix578 joint tree) := by
  rcases exists_fourthDisjointCup_or_privateCupStarSixCapState_at_32
      h458 hreservoir hroot hcard hnoCap hnoCup hnoStrong with
    hfourth | hjoint
  · exact Or.inl hfourth
  · right
    obtain ⟨joint⟩ := hjoint
    obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hreservoir
    exact ⟨joint, tree,
      exists_privateCupSixCapAddressMatrix578 joint tree⟩

/-- Replacing `4 * r` protected vertices of a cup transversal by at most
`3 * r` boundary vertices saves `r` vertices.  The `hits` field below is the
only geometric obligation: every four-cup missed by the unprotected part must
meet the replacement boundary. -/
theorem exists_nineCupTransversal_of_boundary_exchange578
    {n r : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {state : SevenWitnessRegenerationPacking578 χ support}
    (ledger : PrivateCupLedger578 state)
    {protectedSet boundary : Finset (Fin n)}
    (hprotectedSub : protectedSet ⊆ ledger.transversal)
    (hprotectedCard : protectedSet.card = 4 * r)
    (henough : ledger.transversal.card ≤ 9 + r)
    (hboundarySub : boundary ⊆ support)
    (hboundaryCard : boundary.card ≤ 3 * r)
    (hhits : ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
      Disjoint cup (ledger.transversal \ protectedSet) →
        ¬Disjoint cup boundary) :
    ∃ transversal,
      IsCupWitnessTransversal578 χ support transversal 4 ∧
        transversal.card ≤ 9 := by
  let transversal := (ledger.transversal \ protectedSet) ∪ boundary
  refine ⟨transversal, ?_, ?_⟩
  · refine ⟨Finset.union_subset
        (Finset.sdiff_subset.trans ledger.transversal_hits.1)
        hboundarySub, ?_⟩
    intro cup hcup hdisjointUnion
    have hleft : Disjoint cup (ledger.transversal \ protectedSet) :=
      Disjoint.mono_right Finset.subset_union_left hdisjointUnion
    have hright : Disjoint cup boundary :=
      Disjoint.mono_right Finset.subset_union_right hdisjointUnion
    exact (hhits cup hcup hleft) hright
  · dsimp [transversal]
    have hprotectedLe : protectedSet.card ≤ ledger.transversal.card :=
      Finset.card_le_card hprotectedSub
    have hcard :=
      Finset.card_union_le (ledger.transversal \ protectedSet) boundary
    rw [Finset.card_sdiff_of_subset hprotectedSub] at hcard
    omega

/-- The exact remaining tree-geometric contract for the private-star route.
A value of this structure is already enough to turn the current private-cup
ledger into the forbidden nine-vertex transversal. -/
structure PrivateCupBoundaryExchange578
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (joint : PrivateCupStarSixCapState578 χ support) where
  r : ℕ
  protectedSet : Finset (Fin n)
  boundary : Finset (Fin n)
  protectedSet_sub : protectedSet ⊆ joint.ledger.transversal
  protectedSet_card : protectedSet.card = 4 * r
  enough : joint.ledger.transversal.card ≤ 9 + r
  boundary_sub : boundary ⊆ support
  boundary_card : boundary.card ≤ 3 * r
  hits : ∀ cup, cup ∈ capWitnesses χ.dual support 4 →
    Disjoint cup (joint.ledger.transversal \ protectedSet) →
      ¬Disjoint cup boundary

/-- A boundary exchange discharges the exact `≤ 9` transversal target. -/
theorem PrivateCupBoundaryExchange578.exists_nineCupTransversal
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ support}
    (exchange : PrivateCupBoundaryExchange578 joint) :
    ∃ transversal,
      IsCupWitnessTransversal578 χ support transversal 4 ∧
        transversal.card ≤ 9 := by
  exact exists_nineCupTransversal_of_boundary_exchange578
    joint.ledger exchange.protectedSet_sub exchange.protectedSet_card
    exchange.enough exchange.boundary_sub exchange.boundary_card exchange.hits

/-- Under the exact `32/23` density hypotheses, no proposed boundary exchange
can exist: it would contradict the global lower bound of ten for cup
transversals. -/
theorem PrivateCupBoundaryExchange578.false_of_colorDualLower_at_32
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {reservoir : Finset (Fin n)}
    {joint : PrivateCupStarSixCapState578 χ reservoir}
    (exchange : PrivateCupBoundaryExchange578 joint)
    (hreservoir : IsDecomposableOn χ reservoir)
    (hcard : reservoir.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ reservoir) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ reservoir) 8) :
    False := by
  exact not_exists_nine_fourCupTransversal_of_colorDualLower_at_578
    hreservoir hcard hnoCap hnoStrong exchange.exists_nineCupTransversal

end ErdosSzekeres

end
