module

public import ErdosSzekeres.CupCap
public import ErdosSzekeres.HMPTHorizontalColorGeometry
public import ErdosSzekeres.HMPTVerticalProfileProducer
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# The local HMPT horizontal profile

This file constructs actual maximum literal inner and outer subchains of the
horizontal chain stored in an `HMPTVerticalProfile`.  The exact binomial bound
is obtained from the transitive horizontal triple coloring.
-/

namespace ErdosSzekeres

noncomputable section

/-- A private wrapper isolating the horizontal order on one stored chain. -/
private structure HMPTOrderedHorizontalPoint
    {s : Finset (Point 2)} (chain : Finset (↥s)) where
  val : ↥chain
  deriving Fintype

private def hmptOrderedHorizontalPointEquiv
    {s : Finset (Point 2)} (chain : Finset (↥s)) :
    HMPTOrderedHorizontalPoint chain ≃ ↥chain where
  toFun p := p.val
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

private def hmptOrderedHorizontalPointEmbedding
    {s : Finset (Point 2)} (chain : Finset (↥s)) :
    HMPTOrderedHorizontalPoint chain ↪ ↥s where
  toFun p := p.val.1
  inj' := by
    intro p q hpq
    apply (hmptOrderedHorizontalPointEquiv chain).injective
    exact Subtype.ext hpq

private def hmptOrderedHorizontalLT
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (chain : Finset (↥s))
    (p q : HMPTOrderedHorizontalPoint chain) : Prop :=
  HMPTSpikeHorizontalLT outerLeft outerRight p.val.1.1 q.val.1.1

private theorem hmptOrderedHorizontalLT_isStrictTotal
    {s : Finset (Point 2)} {outerLeft outerRight : Point 2}
    (hpair : HMPTSpikeOrderPair outerLeft outerRight s)
    (chain : Finset (↥s))
    (hchain : IsChain
      (fun p q : ↥s ↦ HMPTSpikeHorizontalLE outerLeft outerRight p.1 q.1)
      (chain : Set (↥s))) :
    IsStrictTotalOrder (HMPTOrderedHorizontalPoint chain)
      (hmptOrderedHorizontalLT outerLeft outerRight chain) where
  irrefl p hp := hp.1 rfl
  trans p q r hpq hqr := by
    have hpr := hpair.horizontal_trans p.val.1 q.val.1 r.val.1
      (Or.inr hpq) (Or.inr hqr)
    rcases hpr with hpr | hpr
    · exfalso
      apply hqr.1
      have hrq : HMPTSpikeHorizontalLE outerLeft outerRight
          r.val.1.1 q.val.1.1 := by
        rw [← hpr]
        exact Or.inr hpq
      have hqrEq := hpair.horizontal_antisymm q.val.1 r.val.1
        (Or.inr hqr) hrq
      exact congrArg Subtype.val hqrEq
    · exact hpr
  trichotomous p q hpq hqp := by
    by_contra hpqNe
    have hpqVal : p.val.1 ≠ q.val.1 := by
      intro heq
      apply hpqNe
      apply (hmptOrderedHorizontalPointEquiv chain).injective
      exact Subtype.ext heq
    rcases hchain p.val.property q.val.property hpqVal with hpqLE | hqpLE
    · rcases hpqLE with heq | hlt
      · exact hpqVal (Subtype.ext heq)
      · exact hpq hlt
    · rcases hqpLE with heq | hlt
      · exact hpqVal (Subtype.ext heq.symm)
      · exact hqp hlt

/-- Transitivity propagates a consecutive monochromatic word to every
ordered triple of that word. -/
private theorem hmptHorizontal_allColor_of_consecutive
    {s : Finset (Point 2)} {outerLeft outerRight : Point 2}
    {chain : Finset (↥s)} {color : ↥s → ↥s → ↥s → Turn}
    {c : Turn} {n : ℕ}
    (f : Fin n → HMPTOrderedHorizontalPoint chain)
    (horder : ∀ ⦃i j : Fin n⦄, i < j →
      HMPTSpikeHorizontalLT outerLeft outerRight
        (f i).val.1.1 (f j).val.1.1)
    (htransitive : HMPTHorizontalTransitiveColoring
      outerLeft outerRight color)
    (hlocal : ∀ (i j k : Fin n), (hij : i < j) → (hjk : j < k) →
      j.val = i.val + 1 → k.val = j.val + 1 →
        color (f i).val.1 (f j).val.1 (f k).val.1 = c) :
    ∀ (i j k : Fin n), i < j → j < k →
      color (f i).val.1 (f j).val.1 (f k).val.1 = c := by
  have aux : ∀ span : ℕ, ∀ (i j k : Fin n), k.val - i.val = span →
      (hij : i < j) → (hjk : j < k) →
      color (f i).val.1 (f j).val.1 (f k).val.1 = c := by
    intro span
    induction span using Nat.strong_induction_on with
    | h span ih =>
      intro i j k hspan hij hjk
      by_cases hijSucc : j.val = i.val + 1
      · by_cases hjkSucc : k.val = j.val + 1
        · exact hlocal i j k hij hjk hijSucc hjkSucc
        · let m : Fin n := ⟨k.val - 1, by omega⟩
          have hjm : j < m := by
            change j.val < k.val - 1
            omega
          have hmk : m < k := by
            change k.val - 1 < k.val
            omega
          have hfirst : color (f i).val.1 (f j).val.1 (f m).val.1 = c :=
            ih (m.val - i.val) (by dsimp [m]; omega)
              i j m rfl hij hjm
          have hsecond : color (f j).val.1 (f m).val.1 (f k).val.1 = c :=
            ih (k.val - j.val) (by omega)
              j m k rfl hjm hmk
          exact (htransitive (f i).val.1 (f j).val.1
            (f m).val.1 (f k).val.1
            (horder hij) (horder hjm) (horder hmk)
            c hfirst hsecond).1
      · let m : Fin n := ⟨j.val - 1, by omega⟩
        have him : i < m := by
          change i.val < j.val - 1
          omega
        have hmj : m < j := by
          change j.val - 1 < j.val
          omega
        have hfirst : color (f i).val.1 (f m).val.1 (f j).val.1 = c :=
          ih (j.val - i.val) (by omega)
            i m j rfl him hmj
        have hsecond : color (f m).val.1 (f j).val.1 (f k).val.1 = c :=
          ih (k.val - m.val) (by dsimp [m]; omega)
            m j k rfl hmj hjk
        exact (htransitive (f i).val.1 (f m).val.1
          (f j).val.1 (f k).val.1
          (horder him) (horder hmj) (horder hjk)
          c hfirst hsecond).2
  intro i j k hij hjk
  exact aux (k.val - i.val) i j k rfl hij hjk

private theorem hmptHorizontal_embedding_of_hasNChain
    {s : Finset (Point 2)} {outerLeft outerRight : Point 2}
    {chain : Finset (↥s)} {color : ↥s → ↥s → ↥s → Turn}
    {c : Turn} {k : ℕ} [LinearOrder (HMPTOrderedHorizontalPoint chain)]
    (hstrict : ∀ ⦃p q : HMPTOrderedHorizontalPoint chain⦄, p < q →
      HMPTSpikeHorizontalLT outerLeft outerRight p.val.1.1 q.val.1.1)
    (htransitive : HMPTHorizontalTransitiveColoring
      outerLeft outerRight color)
    (hchain : CupCap.HasNChain
      (fun p q r : HMPTOrderedHorizontalPoint chain ↦
        color p.val.1 q.val.1 r.val.1)
      c k Finset.univ) :
    ∃ f : Fin k ↪o HMPTOrderedHorizontalPoint chain,
      ∀ (i j l : Fin k), i < j → j < l →
        color (f i).val.1 (f j).val.1 (f l).val.1 = c := by
  obtain ⟨l, hturn, hlen, _⟩ := hchain
  subst k
  let f : Fin l.length ↪o HMPTOrderedHorizontalPoint chain :=
    OrderEmbedding.ofStrictMono l.get hturn.1.sortedLT.strictMono_get
  have hlocal : ∀ (i j k : Fin l.length), (hij : i < j) →
      (hjk : j < k) → j.val = i.val + 1 → k.val = j.val + 1 →
        color (f i).val.1 (f j).val.1 (f k).val.1 = c := by
    intro i j k hij hjk hijSucc hjkSucc
    have hi : i.val + 2 < l.length := by omega
    have hcolor := CupCap.consecutive'_getElem hturn.2 i.val hi
    simpa [f, hijSucc, hjkSucc] using hcolor
  refine ⟨f, hmptHorizontal_allColor_of_consecutive f
    (fun {_ _} hij ↦ hstrict (f.strictMono hij)) htransitive hlocal⟩

private theorem exists_literal_horizontal_subchain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (chain : Finset (↥s)) {k : ℕ}
    {P : Finset (Point 2) → Prop}
    [LinearOrder (HMPTOrderedHorizontalPoint chain)]
    (f : Fin k ↪o HMPTOrderedHorizontalPoint chain)
    (hliteral : ∀ (i j l : Fin k), i < j → j < l →
      P {outerLeft, outerRight,
        (f i).val.1.1, (f j).val.1.1, (f l).val.1.1}) :
    ∃ selected : Finset (↥s),
      selected ⊆ chain ∧ selected.card = k ∧
        ∀ triple : Finset (↥s), triple ⊆ selected → triple.card = 3 →
          P (insert outerLeft (insert outerRight (hmptChainPoints triple))) := by
  classical
  let g : Fin k ↪ ↥s :=
    f.toEmbedding.trans (hmptOrderedHorizontalPointEmbedding chain)
  let selected : Finset (↥s) := Finset.univ.image g
  have hgInjective : Function.Injective g := g.injective
  have hselectedSubset : selected ⊆ chain := by
    intro p hp
    simp only [selected, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact (f i).val.property
  have hselectedCard : selected.card = k := by
    calc
      selected.card = (Finset.univ.image g).card := rfl
      _ = (Finset.univ : Finset (Fin k)).card :=
        Finset.card_image_of_injective Finset.univ hgInjective
      _ = k := Finset.card_fin k
  refine ⟨selected, hselectedSubset, hselectedCard, ?_⟩
  intro triple htriple htripleCard
  have htripleImage : triple ⊆ Finset.univ.image g := by
    simpa only [selected] using htriple
  obtain ⟨w, hw⟩ := Finset.subset_univ_image_iff.mp htripleImage
  have hwcard : w.card = 3 := by
    calc
      w.card = (w.image g).card :=
        (Finset.card_image_of_injective w hgInjective).symm
      _ = triple.card := congrArg Finset.card hw
      _ = 3 := htripleCard
  let e : Fin 3 ↪o Fin k := w.orderEmbOfFin hwcard
  have h01 : e 0 < e 1 := e.strictMono (by decide)
  have h12 : e 1 < e 2 := e.strictMono (by decide)
  have hpointsSubtype : ({g (e 0), g (e 1), g (e 2)} : Finset (↥s)) =
      triple := by
    have hfin3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
      decide
    calc
      ({g (e 0), g (e 1), g (e 2)} : Finset (↥s)) =
          Finset.univ.image (g ∘ e) := by
        rw [hfin3]
        simp
      _ = (Finset.univ.image e).image g := by
        rw [Finset.image_image]
      _ = w.image g := by
        rw [Finset.image_orderEmbOfFin_univ]
      _ = triple := hw
  have hpoints : ({(g (e 0)).1, (g (e 1)).1, (g (e 2)).1} :
      Finset (Point 2)) = hmptChainPoints triple := by
    rw [← hpointsSubtype]
    simp [hmptChainPoints]
  have hout := hliteral (e 0) (e 1) (e 2) h01 h12
  change P (insert outerLeft (insert outerRight
    ({(g (e 0)).1, (g (e 1)).1, (g (e 2)).1} : Finset (Point 2)))) at hout
  simpa only [hpoints] using hout

private theorem literal_horizontal_subchain_of_card_le_two
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain selected : Finset (↥s))
    {P : Finset (Point 2) → Prop}
    (hsubset : selected ⊆ horizontalChain) (hcard : selected.card ≤ 2) :
    selected ⊆ horizontalChain ∧
      ∀ triple : Finset (↥s), triple ⊆ selected → triple.card = 3 →
        P (insert outerLeft (insert outerRight (hmptChainPoints triple))) := by
  refine ⟨hsubset, ?_⟩
  intro triple htriple htripleCard
  have hle := Finset.card_le_card htriple
  exfalso
  omega

private theorem exists_maximum_inner_horizontal_subchain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain : Finset (↥s)) :
    ∃ selected : Finset (↥s), HMPTMaximumInnerHorizontalSubchain
      outerLeft outerRight horizontalChain selected := by
  classical
  let candidates : Finset (Finset (↥s)) :=
    horizontalChain.powerset.filter fun selected ↦
      HMPTInnerHorizontalSubchain
        outerLeft outerRight horizontalChain selected
  have hemptyPredicate : HMPTInnerHorizontalSubchain outerLeft outerRight
      horizontalChain (∅ : Finset (↥s)) :=
    literal_horizontal_subchain_of_card_le_two outerLeft outerRight
      horizontalChain ∅ (by simp) (by simp)
  have hempty : (∅ : Finset (↥s)) ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (by simp), hemptyPredicate⟩
  obtain ⟨selected, hselected, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hselectedPredicate := (Finset.mem_filter.mp hselected).2
  refine ⟨selected, hselectedPredicate, ?_⟩
  intro other hother
  apply hmax other
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hother.1, hother⟩

private theorem exists_maximum_outer_horizontal_subchain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain : Finset (↥s)) :
    ∃ selected : Finset (↥s), HMPTMaximumOuterHorizontalSubchain
      outerLeft outerRight horizontalChain selected := by
  classical
  let candidates : Finset (Finset (↥s)) :=
    horizontalChain.powerset.filter fun selected ↦
      HMPTOuterHorizontalSubchain
        outerLeft outerRight horizontalChain selected
  have hemptyPredicate : HMPTOuterHorizontalSubchain outerLeft outerRight
      horizontalChain (∅ : Finset (↥s)) :=
    literal_horizontal_subchain_of_card_le_two outerLeft outerRight
      horizontalChain ∅ (P := fun u ↦ ¬InConvexPosition u)
      (by simp) (by simp)
  have hempty : (∅ : Finset (↥s)) ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (by simp), hemptyPredicate⟩
  obtain ⟨selected, hselected, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card ⟨∅, hempty⟩
  have hselectedPredicate := (Finset.mem_filter.mp hselected).2
  refine ⟨selected, hselectedPredicate, ?_⟩
  intro other hother
  apply hmax other
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hother.1, hother⟩

private theorem inner_horizontal_subchain_of_card_le_two
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain selected : Finset (↥s))
    (hsubset : selected ⊆ horizontalChain) (hcard : selected.card ≤ 2) :
    HMPTInnerHorizontalSubchain
      outerLeft outerRight horizontalChain selected :=
  literal_horizontal_subchain_of_card_le_two outerLeft outerRight
    horizontalChain selected hsubset hcard

private theorem outer_horizontal_subchain_of_card_le_two
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (horizontalChain selected : Finset (↥s))
    (hsubset : selected ⊆ horizontalChain) (hcard : selected.card ≤ 2) :
    HMPTOuterHorizontalSubchain
      outerLeft outerRight horizontalChain selected :=
  literal_horizontal_subchain_of_card_le_two outerLeft outerRight
    horizontalChain selected (P := fun u ↦ ¬InConvexPosition u)
    hsubset hcard

private theorem two_le_maximum_inner_horizontal_card
    {s : Finset (Point 2)} {outerLeft outerRight : Point 2}
    {horizontalChain selected : Finset (↥s)}
    (hchainCard : 2 ≤ horizontalChain.card)
    (hmax : HMPTMaximumInnerHorizontalSubchain
      outerLeft outerRight horizontalChain selected) :
    2 ≤ selected.card := by
  obtain ⟨pair, hpair, hpairCard⟩ :=
    Finset.exists_subset_card_eq hchainCard
  have hpairInner := inner_horizontal_subchain_of_card_le_two
    outerLeft outerRight horizontalChain pair hpair (by omega)
  have hbound := hmax.2 pair hpairInner
  omega

private theorem two_le_maximum_outer_horizontal_card
    {s : Finset (Point 2)} {outerLeft outerRight : Point 2}
    {horizontalChain selected : Finset (↥s)}
    (hchainCard : 2 ≤ horizontalChain.card)
    (hmax : HMPTMaximumOuterHorizontalSubchain
      outerLeft outerRight horizontalChain selected) :
    2 ≤ selected.card := by
  obtain ⟨pair, hpair, hpairCard⟩ :=
    Finset.exists_subset_card_eq hchainCard
  have hpairOuter := outer_horizontal_subchain_of_card_le_two
    outerLeft outerRight horizontalChain pair hpair (by omega)
  have hbound := hmax.2 pair hpairOuter
  omega

namespace SukRegionGeometry

variable {outerLeft rightAnchor leftAnchor outerRight : Point 2}
  {s : Finset (Point 2)}

private theorem horizontalCard_le_choose_f3
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s)
    (innerChain outerChain : Finset (↥s))
    (hinner : HMPTMaximumInnerHorizontalSubchain outerLeft outerRight
      verticalProfile.horizontalChain innerChain)
    (houter : HMPTMaximumOuterHorizontalSubchain outerLeft outerRight
      verticalProfile.horizontalChain outerChain) :
    verticalProfile.horizontalChain.card ≤
      Nat.choose (innerChain.card + outerChain.card - 2)
        (innerChain.card - 1) := by
  classical
  by_cases hsmall : verticalProfile.horizontalChain.card ≤ 2
  · have hinnerWhole := inner_horizontal_subchain_of_card_le_two
      outerLeft outerRight verticalProfile.horizontalChain
      verticalProfile.horizontalChain (fun _ hp ↦ hp) hsmall
    have houterWhole := outer_horizontal_subchain_of_card_le_two
      outerLeft outerRight verticalProfile.horizontalChain
      verticalProfile.horizontalChain (fun _ hp ↦ hp) hsmall
    have hhorizontal_le_inner :=
      hinner.2 verticalProfile.horizontalChain hinnerWhole
    have hinner_le_horizontal := Finset.card_le_card hinner.1.1
    have hhorizontal_le_outer :=
      houter.2 verticalProfile.horizontalChain houterWhole
    have houter_le_horizontal := Finset.card_le_card houter.1.1
    have hinnerCard : innerChain.card =
        verticalProfile.horizontalChain.card := by omega
    have houterCard : outerChain.card =
        verticalProfile.horizontalChain.card := by omega
    interval_cases hhorizontalCard : verticalProfile.horizontalChain.card <;>
      simp [hinnerCard, houterCard]
  · have hlarge : 3 ≤ verticalProfile.horizontalChain.card := by omega
    have hinnerTwo : 2 ≤ innerChain.card :=
      two_le_maximum_inner_horizontal_card (by omega) hinner
    have houterTwo : 2 ≤ outerChain.card :=
      two_le_maximum_outer_horizontal_card (by omega) houter
    by_contra hbound
    have hchooseLt :
        Nat.choose (innerChain.card + outerChain.card - 2)
            (innerChain.card - 1) <
          verticalProfile.horizontalChain.card := by
      omega
    let horizontalLT := hmptOrderedHorizontalLT outerLeft outerRight
      verticalProfile.horizontalChain
    letI : DecidableRel horizontalLT := Classical.decRel _
    letI : IsStrictTotalOrder
        (HMPTOrderedHorizontalPoint verticalProfile.horizontalChain)
        horizontalLT :=
      hmptOrderedHorizontalLT_isStrictTotal h.toHMPTSpikeOrderPair
        verticalProfile.horizontalChain verticalProfile.horizontalMaximum.1
    letI : LinearOrder
        (HMPTOrderedHorizontalPoint verticalProfile.horizontalChain) :=
      linearOrderOfSTO horizontalLT
    have hstrict : ∀ ⦃p q :
        HMPTOrderedHorizontalPoint verticalProfile.horizontalChain⦄,
        p < q → HMPTSpikeHorizontalLT outerLeft outerRight
          p.val.1.1 q.val.1.1 := by
      intro p q hpq
      exact hpq
    have horderedCard : Fintype.card
        (HMPTOrderedHorizontalPoint verticalProfile.horizontalChain) =
        verticalProfile.horizontalChain.card := by
      rw [Fintype.card_congr
        (hmptOrderedHorizontalPointEquiv verticalProfile.horizontalChain),
        Fintype.card_coe]
    have hunivCard :
        (Finset.univ : Finset
          (HMPTOrderedHorizontalPoint verticalProfile.horizontalChain)).card =
          verticalProfile.horizontalChain.card := by
      simpa only [Finset.card_univ] using horderedCard
    have hcupBound :
        Nat.choose
            ((innerChain.card - 1) + (outerChain.card - 1))
            (innerChain.card - 1) <
          (Finset.univ : Finset
            (HMPTOrderedHorizontalPoint
              verticalProfile.horizontalChain)).card := by
      rw [show (innerChain.card - 1) + (outerChain.card - 1) =
          innerChain.card + outerChain.card - 2 by omega]
      rw [hunivCard]
      exact hchooseLt
    have hgeometry := h.hmptHorizontalTripleGeometry
    have halt := CupCap.cup_cap
      (fun p q r :
          HMPTOrderedHorizontalPoint verticalProfile.horizontalChain ↦
        hmptHorizontalTripleColor p.val.1 q.val.1 r.val.1)
      (innerChain.card - 1) (outerChain.card - 1)
      Finset.univ hcupBound
    rcases halt with hright | hleft
    · have hright' : CupCap.HasNChain
          (fun p q r :
              HMPTOrderedHorizontalPoint verticalProfile.horizontalChain ↦
            hmptHorizontalTripleColor p.val.1 q.val.1 r.val.1)
          Turn.right (innerChain.card + 1) Finset.univ := by
        simpa only [show innerChain.card - 1 + 2 =
          innerChain.card + 1 by omega] using hright
      obtain ⟨f, hall⟩ := hmptHorizontal_embedding_of_hasNChain
        hstrict hgeometry.transitive hright'
      obtain ⟨other, hotherSubset, hotherCard, hotherLiteral⟩ :=
        exists_literal_horizontal_subchain outerLeft outerRight
          verticalProfile.horizontalChain f (P := InConvexPosition) (by
            intro i j l hij hjl
            exact (hgeometry.semantics
              (f i).val.1 (f j).val.1 (f l).val.1
              (hstrict (f.strictMono hij))
              (hstrict (f.strictMono hjl))).1.mp
                (hall i j l hij hjl))
      have hotherInner : HMPTInnerHorizontalSubchain outerLeft outerRight
          verticalProfile.horizontalChain other :=
        ⟨hotherSubset, hotherLiteral⟩
      have hmax := hinner.2 other hotherInner
      omega
    · have hleft' : CupCap.HasNChain
          (fun p q r :
              HMPTOrderedHorizontalPoint verticalProfile.horizontalChain ↦
            hmptHorizontalTripleColor p.val.1 q.val.1 r.val.1)
          Turn.left (outerChain.card + 1) Finset.univ := by
        simpa only [show outerChain.card - 1 + 2 =
          outerChain.card + 1 by omega] using hleft
      obtain ⟨f, hall⟩ := hmptHorizontal_embedding_of_hasNChain
        hstrict hgeometry.transitive hleft'
      obtain ⟨other, hotherSubset, hotherCard, hotherLiteral⟩ :=
        exists_literal_horizontal_subchain outerLeft outerRight
          verticalProfile.horizontalChain f
          (P := fun u ↦ ¬InConvexPosition u) (by
            intro i j l hij hjl
            exact (hgeometry.semantics
              (f i).val.1 (f j).val.1 (f l).val.1
              (hstrict (f.strictMono hij))
              (hstrict (f.strictMono hjl))).2.mp
                (hall i j l hij hjl))
      have hotherOuter : HMPTOuterHorizontalSubchain outerLeft outerRight
          verticalProfile.horizontalChain other :=
        ⟨hotherSubset, hotherLiteral⟩
      have hmax := houter.2 other hotherOuter
      omega

/-- Raw region geometry and an existing vertical profile produce actual
maximum literal horizontal subchains satisfying the exact recurrence bound. -/
theorem exists_hmptHorizontalProfile
    (h : SukRegionGeometry
      outerLeft rightAnchor leftAnchor outerRight s)
    (verticalProfile : HMPTVerticalProfile
      outerLeft rightAnchor leftAnchor outerRight s) :
    Nonempty (HMPTHorizontalProfile
      outerLeft rightAnchor leftAnchor outerRight s verticalProfile) := by
  classical
  obtain ⟨innerChain, hinner⟩ :=
    exists_maximum_inner_horizontal_subchain outerLeft outerRight
      verticalProfile.horizontalChain
  obtain ⟨outerChain, houter⟩ :=
    exists_maximum_outer_horizontal_subchain outerLeft outerRight
      verticalProfile.horizontalChain
  exact ⟨{
    innerChain := innerChain
    outerChain := outerChain
    innerMaximum := hinner
    outerMaximum := houter
    horizontalCard_le_choose :=
      h.horizontalCard_le_choose_f3 verticalProfile innerChain outerChain
        hinner houter
  }⟩

end SukRegionGeometry

end

end ErdosSzekeres

end
