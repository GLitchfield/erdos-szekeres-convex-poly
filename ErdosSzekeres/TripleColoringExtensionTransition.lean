module

public import ErdosSzekeres.TripleColoringExtensionFiber

@[expose] public section

/-!
# Permutation transitions for two consecutive right extensions

A compatible right-extension link is a transitive tournament, hence is represented by a
permutation of the old vertices.  For two consecutive rightmost vertices, the connector colors
split both link permutations into the same two intervals.  Inside either interval, link
disagreements have only one direction.

These are consequences of the abstract one-change law.  No realizability or target-avoidance
hypothesis is used.
-/

namespace ErdosSzekeres

noncomputable section

namespace Turn

/-- The other one of the two turn colors. -/
def other : Turn → Turn
  | .left => .right
  | .right => .left

@[simp] theorem other_left : Turn.left.other = Turn.right := rfl

@[simp] theorem other_right : Turn.right.other = Turn.left := rfl

@[simp] theorem other_other (c : Turn) : c.other.other = c := by
  cases c <;> rfl

end Turn

namespace RightExtensionLink

/-- The tournament relation encoded by a pair link.  On an increasing pair, `left` points
forward and `right` points backward. -/
def Precedes {n : ℕ} (link : RightExtensionLink n) (i j : Fin n) : Prop :=
  (∃ hij : i < j, link ⟨i, j, hij⟩ = Turn.left) ∨
    ∃ hji : j < i, link ⟨j, i, hji⟩ = Turn.right

/-- A permutation represents a link when its rank order is the link tournament. -/
def RepresentedBy {n : ℕ} (link : RightExtensionLink n) (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ p, link p = Turn.left ↔ π p.i < π p.j

/-- The ternary condition on a pair link obtained by forgetting the first color in each
one-change word. -/
def OneChangeCompatible {n : ℕ} (link : RightExtensionLink n) : Prop :=
  ∀ {i j k : Fin n}, (hij : i < j) → (hjk : j < k) →
    ∃ root : Turn,
      TurnSequenceAllowed root (link ⟨i, j, hij⟩)
        (link ⟨i, k, hij.trans hjk⟩) (link ⟨j, k, hjk⟩)

@[simp] theorem precedes_iff_of_lt {n : ℕ} {link : RightExtensionLink n}
    {i j : Fin n} (hij : i < j) :
    link.Precedes i j ↔ link ⟨i, j, hij⟩ = Turn.left := by
  simp [Precedes, hij, not_lt_of_ge hij.le]

@[simp] theorem precedes_reverse_iff_of_lt {n : ℕ} {link : RightExtensionLink n}
    {i j : Fin n} (hij : i < j) :
    link.Precedes j i ↔ link ⟨i, j, hij⟩ = Turn.right := by
  simp [Precedes, hij, not_lt_of_ge hij.le]

theorem precedes_irrefl {n : ℕ} (link : RightExtensionLink n) :
    ∀ i, ¬link.Precedes i i := by
  intro i hii
  rcases hii with hii | hii
  · exact (lt_irrefl i hii.choose)
  · exact (lt_irrefl i hii.choose)

theorem precedes_asymm {n : ℕ} (link : RightExtensionLink n) :
    ∀ ⦃i j⦄, link.Precedes i j → ¬link.Precedes j i := by
  intro i j hij hji
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have hleft := (precedes_iff_of_lt hlt).mp hij
    have hright := (precedes_reverse_iff_of_lt hlt).mp hji
    rw [hleft] at hright
    exact Turn.noConfusion hright
  · exact link.precedes_irrefl i hij
  · have hright := (precedes_reverse_iff_of_lt hgt).mp hij
    have hleft := (precedes_iff_of_lt hgt).mp hji
    rw [hleft] at hright
    exact Turn.noConfusion hright.symm

theorem precedes_total {n : ℕ} (link : RightExtensionLink n) :
    ∀ i j, link.Precedes i j ∨ i = j ∨ link.Precedes j i := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases hcolor : link ⟨i, j, hij⟩ with
    | left => exact Or.inl ((precedes_iff_of_lt hij).mpr hcolor)
    | right => exact Or.inr (Or.inr ((precedes_reverse_iff_of_lt hij).mpr hcolor))
  · exact Or.inr (Or.inl rfl)
  · cases hcolor : link ⟨j, i, hji⟩ with
    | left => exact Or.inr (Or.inr ((precedes_iff_of_lt hji).mpr hcolor))
    | right => exact Or.inl ((precedes_reverse_iff_of_lt hji).mpr hcolor)

/-- The two cyclic color patterns are exactly the two forbidden restrictions of a
one-change word to its final three positions. -/
theorem forbidden_cyclic_triples {n : ℕ} {link : RightExtensionLink n}
    (hlink : link.OneChangeCompatible) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) :
    ¬(link ⟨i, j, hij⟩ = Turn.left ∧
        link ⟨i, k, hij.trans hjk⟩ = Turn.right ∧
        link ⟨j, k, hjk⟩ = Turn.left) ∧
      ¬(link ⟨i, j, hij⟩ = Turn.right ∧
        link ⟨i, k, hij.trans hjk⟩ = Turn.left ∧
        link ⟨j, k, hjk⟩ = Turn.right) := by
  obtain ⟨root, hallowed⟩ := hlink hij hjk
  constructor <;> intro hcycle <;> rcases hcycle with ⟨h₁, h₂, h₃⟩ <;>
    cases root <;> simp_all [TurnSequenceAllowed]

theorem no_precedes_three_cycle {n : ℕ} {link : RightExtensionLink n}
    (hlink : link.OneChangeCompatible) {a b c : Fin n} :
    ¬(link.Precedes a b ∧ link.Precedes b c ∧ link.Precedes c a) := by
  rintro ⟨hab, hbc, hca⟩
  have habne : a ≠ b := fun h ↦ by
    subst b
    exact link.precedes_irrefl a hab
  have hbcne : b ≠ c := fun h ↦ by
    subst c
    exact link.precedes_irrefl b hbc
  have hacne : a ≠ c := fun h ↦ by
    subst c
    exact (link.precedes_asymm hab) hbc
  rcases lt_or_gt_of_ne habne with hablt | hbalt
  · rcases lt_or_gt_of_ne hbcne with hbclt | hcblt
    · apply (forbidden_cyclic_triples hlink hablt hbclt).1
      exact ⟨(precedes_iff_of_lt hablt).mp hab,
        (precedes_reverse_iff_of_lt (hablt.trans hbclt)).mp hca,
        (precedes_iff_of_lt hbclt).mp hbc⟩
    · rcases lt_or_gt_of_ne hacne with haclt | hcalt
      · apply (forbidden_cyclic_triples hlink haclt hcblt).2
        exact ⟨(precedes_reverse_iff_of_lt haclt).mp hca,
          (precedes_iff_of_lt hablt).mp hab,
          (precedes_reverse_iff_of_lt hcblt).mp hbc⟩
      · apply (forbidden_cyclic_triples hlink hcalt hablt).1
        exact ⟨(precedes_iff_of_lt hcalt).mp hca,
          (precedes_reverse_iff_of_lt (hcalt.trans hablt)).mp hbc,
          (precedes_iff_of_lt hablt).mp hab⟩
  · rcases lt_or_gt_of_ne hbcne with hbclt | hcblt
    · rcases lt_or_gt_of_ne hacne with haclt | hcalt
      · apply (forbidden_cyclic_triples hlink hbalt haclt).2
        exact ⟨(precedes_reverse_iff_of_lt hbalt).mp hab,
          (precedes_iff_of_lt hbclt).mp hbc,
          (precedes_reverse_iff_of_lt haclt).mp hca⟩
      · apply (forbidden_cyclic_triples hlink hbclt hcalt).1
        exact ⟨(precedes_iff_of_lt hbclt).mp hbc,
          (precedes_reverse_iff_of_lt (hbclt.trans hcalt)).mp hab,
          (precedes_iff_of_lt hcalt).mp hca⟩
    · apply (forbidden_cyclic_triples hlink hcblt hbalt).2
      exact ⟨(precedes_reverse_iff_of_lt hcblt).mp hbc,
        (precedes_iff_of_lt (hcblt.trans hbalt)).mp hca,
        (precedes_reverse_iff_of_lt hbalt).mp hab⟩

theorem precedes_transitive {n : ℕ} {link : RightExtensionLink n}
    (hlink : link.OneChangeCompatible) :
    ∀ ⦃a b c⦄, link.Precedes a b → link.Precedes b c → link.Precedes a c := by
  intro a b c hab hbc
  rcases link.precedes_total a c with hac | rfl | hca
  · exact hac
  · exact ((link.precedes_asymm hab) hbc).elim
  · exact (no_precedes_three_cycle hlink ⟨hab, hbc, hca⟩).elim

theorem precedes_isStrictTotalOrder {n : ℕ} {link : RightExtensionLink n}
    (hlink : link.OneChangeCompatible) : IsStrictTotalOrder (Fin n) link.Precedes where
  trichotomous i j hij hji := by
    rcases link.precedes_total i j with h | h | h
    · exact (hij h).elim
    · exact h
    · exact (hji h).elim
  irrefl := link.precedes_irrefl
  trans := precedes_transitive hlink

/-- Membership in the existing abstract link fiber supplies the ternary link condition. -/
theorem oneChangeCompatible_of_mem_abstractFiber {n : ℕ} {χ : TripleColoring n}
    {link : RightExtensionLink n} (hlink : link ∈ AbstractRightExtensionLinkFiber χ) :
    link.OneChangeCompatible := by
  intro i j k hij hjk
  exact ⟨χ ⟨i, j, k, hij, hjk⟩, hlink hij hjk⟩

end RightExtensionLink

private structure LinkOrderVertex (n : ℕ) where
  val : Fin n
  deriving DecidableEq, Fintype

private def linkOrderVertexEquiv (n : ℕ) : Fin n ≃ LinkOrderVertex n where
  toFun i := ⟨i⟩
  invFun i := i.val
  left_inv _ := rfl
  right_inv _ := rfl

private def LinkOrderVertex.precedes {n : ℕ} (link : RightExtensionLink n)
    (i j : LinkOrderVertex n) : Prop :=
  link.Precedes i.val j.val

private theorem LinkOrderVertex.precedes_isStrictTotalOrder {n : ℕ}
    {link : RightExtensionLink n} (hlink : link.OneChangeCompatible) :
    IsStrictTotalOrder (LinkOrderVertex n) (LinkOrderVertex.precedes link) where
  trichotomous i j hij hji := by
    rcases link.precedes_total i.val j.val with h | h | h
    · exact (hij h).elim
    · apply (linkOrderVertexEquiv n).symm.injective
      exact h
    · exact (hji h).elim
  irrefl i := link.precedes_irrefl i.val
  trans _ _ _ hij hjk := RightExtensionLink.precedes_transitive hlink hij hjk

private theorem oneChangeCompatible_hasPermutation {n : ℕ} {link : RightExtensionLink n}
    (hcompatible : link.OneChangeCompatible) :
    ∃ π : Equiv.Perm (Fin n), link.RepresentedBy π := by
  let relation := LinkOrderVertex.precedes link
  letI : IsStrictTotalOrder (LinkOrderVertex n) relation :=
    LinkOrderVertex.precedes_isStrictTotalOrder hcompatible
  letI : DecidableRel relation := Classical.decRel relation
  letI : LinearOrder (LinkOrderVertex n) := linearOrderOfSTO relation
  have hcard : Fintype.card (LinkOrderVertex n) = n := by
    simpa using Fintype.card_congr (linkOrderVertexEquiv n).symm
  let orderEquiv : Fin n ≃o LinkOrderVertex n :=
    Fintype.orderIsoFinOfCardEq (LinkOrderVertex n) hcard
  let π : Equiv.Perm (Fin n) :=
    (linkOrderVertexEquiv n).trans orderEquiv.symm.toEquiv
  refine ⟨π, ?_⟩
  intro p
  have hrank :
      orderEquiv.symm (linkOrderVertexEquiv n p.i) <
          orderEquiv.symm (linkOrderVertexEquiv n p.j) ↔
        (linkOrderVertexEquiv n p.i) < (linkOrderVertexEquiv n p.j) :=
    orderEquiv.symm.lt_iff_lt
  change link p = Turn.left ↔
    orderEquiv.symm (linkOrderVertexEquiv n p.i) <
      orderEquiv.symm (linkOrderVertexEquiv n p.j)
  rw [hrank]
  change link p = Turn.left ↔ link.Precedes p.i p.j
  exact (RightExtensionLink.precedes_iff_of_lt p.hij).symm

/-- Every abstract compatible right-extension link is genuinely the tournament of a permutation
of the old vertices. -/
theorem compatibleRightExtensionLink_hasPermutation {n : ℕ} {χ : TripleColoring n}
    {link : RightExtensionLink n} (hlink : link ∈ AbstractRightExtensionLinkFiber χ) :
    ∃ π : Equiv.Perm (Fin n), link.RepresentedBy π :=
  oneChangeCompatible_hasPermutation
    (RightExtensionLink.oneChangeCompatible_of_mem_abstractFiber hlink)

namespace RightExtensionLink

theorem right_iff_of_representedBy {n : ℕ} {link : RightExtensionLink n}
    {π : Equiv.Perm (Fin n)} (hπ : link.RepresentedBy π) (p : OrderedPair n) :
    link p = Turn.right ↔ π p.j < π p.i := by
  have hne : π p.i ≠ π p.j := π.injective.ne (ne_of_lt p.hij)
  constructor
  · intro hright
    have hnleft : link p ≠ Turn.left := by simp [hright]
    have hnlt : ¬π p.i < π p.j := fun h ↦ hnleft ((hπ p).mpr h)
    omega
  · intro hji
    cases hcolor : link p with
    | left =>
        have hij := (hπ p).mp hcolor
        omega
    | right => rfl

end RightExtensionLink

namespace TripleColoring

/-- The old-pair link through the penultimate vertex. -/
def penultimateRightExtensionLink {n : ℕ} (ψ : TripleColoring (n + 2)) :
    RightExtensionLink n :=
  (ψ.restrict (finInitialOrderEmbedding (n + 1))).rightExtensionLink

/-- The old-pair part of the link through the final vertex. -/
def finalRightExtensionLinkOnInitial {n : ℕ} (ψ : TripleColoring (n + 2)) :
    RightExtensionLink n :=
  fun p ↦ ψ.rightExtensionLink
    ⟨p.i.castSucc, p.j.castSucc, Fin.castSucc_lt_castSucc_iff.mpr p.hij⟩

/-- The color of the triple consisting of one old vertex and the two new rightmost vertices. -/
def rightExtensionConnectorColor {n : ℕ} (ψ : TripleColoring (n + 2)) (i : Fin n) : Turn :=
  ψ.rightExtensionLink ⟨i.castSucc, Fin.last n, Fin.castSucc_lt_last i⟩

end TripleColoring

/-- A color fiber is an interval in the rank order of a permutation. -/
def ConnectorFiberIsInterval {n : ℕ} (π : Equiv.Perm (Fin n))
    (σ : Fin n → Turn) (c : Turn) : Prop :=
  ∀ ⦃a b z : Fin n⦄, σ a = c → σ b = c →
    ((π a ≤ π z ∧ π z ≤ π b) ∨ (π b ≤ π z ∧ π z ≤ π a)) → σ z = c

/-- The exact three possibilities for a pair inside a connector-color block. -/
def BlockwiseOneDirectionalTransition {n : ℕ} (lambda mu : RightExtensionLink n)
    (σ : Fin n → Turn) : Prop :=
  ∀ ⦃i j : Fin n⦄, (hij : i < j) → ∀ c : Turn, σ i = c → σ j = c →
    (lambda ⟨i, j, hij⟩ = c ∧ mu ⟨i, j, hij⟩ = c) ∨
      (lambda ⟨i, j, hij⟩ = c.other ∧ mu ⟨i, j, hij⟩ = c.other) ∨
      (lambda ⟨i, j, hij⟩ = c.other ∧ mu ⟨i, j, hij⟩ = c)

/-- A disagreement inside a connector block has the unique direction `other c` to `c`. -/
theorem BlockwiseOneDirectionalTransition.eq_other_and_eq_of_ne {n : ℕ}
    {lambda mu : RightExtensionLink n} {σ : Fin n → Turn}
    (htransition : BlockwiseOneDirectionalTransition lambda mu σ)
    {i j : Fin n} (hij : i < j) (c : Turn) (hi : σ i = c) (hj : σ j = c)
    (hne : lambda ⟨i, j, hij⟩ ≠ mu ⟨i, j, hij⟩) :
    lambda ⟨i, j, hij⟩ = c.other ∧ mu ⟨i, j, hij⟩ = c := by
  rcases htransition hij c hi hj with hsame | hsame | hchange
  · exact (hne (hsame.1.trans hsame.2.symm)).elim
  · exact (hne (hsame.1.trans hsame.2.symm)).elim
  · exact hchange

private theorem connectorFiberIsInterval_of_leftBeforeRight {n : ℕ}
    (π : Equiv.Perm (Fin n)) (σ : Fin n → Turn)
    (hblocks : ∀ i j, σ i = Turn.left → σ j = Turn.right → π i < π j) :
    ∀ c, ConnectorFiberIsInterval π σ c := by
  intro c a b z ha hb hz
  cases c <;> cases hσz : σ z
  · rfl
  · have haz := hblocks a z ha hσz
    have hbz := hblocks b z hb hσz
    rcases hz with hz | hz <;> omega
  · have hza := hblocks z a hσz ha
    have hzb := hblocks z b hσz hb
    rcases hz with hz | hz <;> omega
  · rfl

private theorem blockwiseTransition_of_fourWord {n : ℕ}
    (lambda mu : RightExtensionLink n) (σ : Fin n → Turn)
    (hfour : ∀ {i j : Fin n}, (hij : i < j) →
      TurnSequenceAllowed (lambda ⟨i, j, hij⟩) (mu ⟨i, j, hij⟩) (σ i) (σ j)) :
    BlockwiseOneDirectionalTransition lambda mu σ := by
  intro i j hij c hi hj
  have hallowed := hfour hij
  cases c <;> cases hlambda : lambda ⟨i, j, hij⟩ <;>
    cases hmu : mu ⟨i, j, hij⟩ <;> simp_all [TurnSequenceAllowed]

private theorem fourWord_head_eq_of_connector_ne {a b c d : Turn}
    (hallowed : TurnSequenceAllowed a b c d) (hcd : c ≠ d) :
    a = b ∧ b = c := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [TurnSequenceAllowed]

/-- The exact permutation, common-interval, four-word, and blockwise inversion law for two
consecutive right extensions. -/
theorem compatibleRightExtensionLinks_connectorBlockLaw {n : ℕ}
    (ψ : TripleColoring (n + 2)) (hone : OneChangeOn ψ Finset.univ) :
    ∃ πLambda πMu : Equiv.Perm (Fin n),
      ψ.penultimateRightExtensionLink.RepresentedBy πLambda ∧
      ψ.finalRightExtensionLinkOnInitial.RepresentedBy πMu ∧
      (∀ i j, ψ.rightExtensionConnectorColor i = Turn.left →
        ψ.rightExtensionConnectorColor j = Turn.right →
        πLambda i < πLambda j ∧ πMu i < πMu j) ∧
      (∀ c, ConnectorFiberIsInterval πLambda ψ.rightExtensionConnectorColor c) ∧
      (∀ c, ConnectorFiberIsInterval πMu ψ.rightExtensionConnectorColor c) ∧
      (∀ {i j : Fin n}, (hij : i < j) →
        TurnSequenceAllowed (ψ.penultimateRightExtensionLink ⟨i, j, hij⟩)
          (ψ.finalRightExtensionLinkOnInitial ⟨i, j, hij⟩)
          (ψ.rightExtensionConnectorColor i) (ψ.rightExtensionConnectorColor j)) ∧
      BlockwiseOneDirectionalTransition ψ.penultimateRightExtensionLink
        ψ.finalRightExtensionLinkOnInitial ψ.rightExtensionConnectorColor := by
  let lambda := ψ.penultimateRightExtensionLink
  let mu := ψ.finalRightExtensionLinkOnInitial
  let σ := ψ.rightExtensionConnectorColor
  have hlambdaCompatible : lambda.OneChangeCompatible := by
    intro i j k hij hjk
    refine ⟨ψ ⟨i.castSucc.castSucc, j.castSucc.castSucc, k.castSucc.castSucc,
      by simpa using hij, by simpa using hjk⟩, ?_⟩
    have h := hone
      (i := i.castSucc.castSucc) (j := j.castSucc.castSucc)
      (k := k.castSucc.castSucc) (l := (Fin.last n).castSucc)
      (by simpa using hij) (by simpa using hjk) (by simp)
      (by simp) (by simp) (by simp) (by simp)
    simpa [lambda, TripleColoring.penultimateRightExtensionLink,
      TripleColoring.rightExtensionLink, TripleColoring.lastPairColor,
      TripleColoring.restrict, OrderedTriple.map, finInitialOrderEmbedding] using h
  have hmuCompatible : mu.OneChangeCompatible := by
    intro i j k hij hjk
    refine ⟨ψ ⟨i.castSucc.castSucc, j.castSucc.castSucc, k.castSucc.castSucc,
      by simpa using hij, by simpa using hjk⟩, ?_⟩
    have h := hone
      (i := i.castSucc.castSucc) (j := j.castSucc.castSucc)
      (k := k.castSucc.castSucc) (l := Fin.last (n + 1))
      (by simpa using hij) (by simpa using hjk) (by simp)
      (by simp) (by simp) (by simp) (by simp)
    simpa [mu, TripleColoring.finalRightExtensionLinkOnInitial,
      TripleColoring.rightExtensionLink, TripleColoring.lastPairColor] using h
  obtain ⟨πLambda, hπLambda⟩ := oneChangeCompatible_hasPermutation hlambdaCompatible
  obtain ⟨πMu, hπMu⟩ := oneChangeCompatible_hasPermutation hmuCompatible
  have hfour : ∀ {i j : Fin n}, (hij : i < j) →
      TurnSequenceAllowed (lambda ⟨i, j, hij⟩) (mu ⟨i, j, hij⟩) (σ i) (σ j) := by
    intro i j hij
    have h := hone
      (i := i.castSucc.castSucc) (j := j.castSucc.castSucc)
      (k := (Fin.last n).castSucc) (l := Fin.last (n + 1))
      (by simpa using hij) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
    simpa [lambda, mu, σ, TripleColoring.penultimateRightExtensionLink,
      TripleColoring.finalRightExtensionLinkOnInitial,
      TripleColoring.rightExtensionConnectorColor, TripleColoring.rightExtensionLink,
      TripleColoring.lastPairColor, TripleColoring.restrict, OrderedTriple.map,
      finInitialOrderEmbedding] using h
  have hblocksLambda : ∀ i j, σ i = Turn.left → σ j = Turn.right →
      πLambda i < πLambda j := by
    intro i j hi hj
    have hijne : i ≠ j := by
      intro h
      subst j
      simp_all
    rcases lt_or_gt_of_ne hijne with hij | hji
    · have hhead := fourWord_head_eq_of_connector_ne (hfour hij) (by simp_all)
      exact (hπLambda ⟨i, j, hij⟩).mp (hhead.1.trans (hhead.2.trans hi))
    · have hhead := fourWord_head_eq_of_connector_ne (hfour hji) (by simp_all)
      have hright : lambda ⟨j, i, hji⟩ = Turn.right :=
        hhead.1.trans (hhead.2.trans hj)
      exact (RightExtensionLink.right_iff_of_representedBy hπLambda ⟨j, i, hji⟩).mp
        hright
  have hblocksMu : ∀ i j, σ i = Turn.left → σ j = Turn.right →
      πMu i < πMu j := by
    intro i j hi hj
    have hijne : i ≠ j := by
      intro h
      subst j
      simp_all
    rcases lt_or_gt_of_ne hijne with hij | hji
    · have hhead := fourWord_head_eq_of_connector_ne (hfour hij) (by simp_all)
      exact (hπMu ⟨i, j, hij⟩).mp (hhead.2.trans hi)
    · have hhead := fourWord_head_eq_of_connector_ne (hfour hji) (by simp_all)
      have hright : mu ⟨j, i, hji⟩ = Turn.right := hhead.2.trans hj
      exact (RightExtensionLink.right_iff_of_representedBy hπMu ⟨j, i, hji⟩).mp hright
  refine ⟨πLambda, πMu, hπLambda, hπMu, ?_, ?_, ?_, hfour, ?_⟩
  · intro i j hi hj
    exact ⟨hblocksLambda i j hi hj, hblocksMu i j hi hj⟩
  · exact connectorFiberIsInterval_of_leftBeforeRight πLambda σ hblocksLambda
  · exact connectorFiberIsInterval_of_leftBeforeRight πMu σ hblocksMu
  · exact blockwiseTransition_of_fourWord lambda mu σ hfour

end

end ErdosSzekeres

end
