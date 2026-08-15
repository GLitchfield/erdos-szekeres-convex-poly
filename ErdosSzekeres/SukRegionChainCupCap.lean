module

public import ErdosSzekeres.CupCap
public import ErdosSzekeres.SukRegionOrder
public import ErdosSzekeres.SukAdjacentSupportProducer

@[expose] public section

/-!
# Transitive cup/cap selection on a Suk region chain

This module isolates the finite source-level recurrence used on one totally
ordered Suk support region.  Its geometric meaning is explicit: a color says
which anchor makes each ordered triple convex.  The final section separately
states the still-open global choice needed in two adjacent regions and proves
that such a choice feeds the existing certificate construction.
-/

namespace ErdosSzekeres

noncomputable section

/-- The strict part of the triangle-containment order in a Suk support region. -/
def SukRegionLT (outerLeft outerRight p q : Point 2) : Prop :=
  SukRegionLE outerLeft outerRight p q ∧
    ¬SukRegionLE outerLeft outerRight q p

/-- The source's four-point transitivity law for the two triple colors. -/
def SukRegionTransitiveTwoColoring
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (color : (↥s) → (↥s) → (↥s) → Turn) : Prop :=
  ∀ p q r t : ↥s, SukRegionLT outerLeft outerRight p q →
    SukRegionLT outerLeft outerRight q r →
    SukRegionLT outerLeft outerRight r t →
    ∀ c : Turn, color p q r = c → color q r t = c →
      color p q t = c ∧ color p r t = c

/-- The exact anchor interpretation of the two colors on ordered region triples. -/
def SukRegionTwoColorSemantics
    {s : Finset (Point 2)}
    (rightAnchor leftAnchor outerLeft outerRight : Point 2)
    (color : (↥s) → (↥s) → (↥s) → Turn) : Prop :=
  ∀ p q r : ↥s, SukRegionLT outerLeft outerRight p q →
    SukRegionLT outerLeft outerRight q r →
      (color p q r = Turn.right ↔
        InConvexPosition {rightAnchor, p.1, q.1, r.1}) ∧
      (color p q r = Turn.left ↔
        InConvexPosition {leftAnchor, p.1, q.1, r.1})

/-- An ordered selected region chain whose every triple has one source color
and extends the corresponding anchor to a convex quadruple. -/
def SukRegionHasAnchoredColorChain
    {s : Finset (Point 2)} (outerLeft outerRight : Point 2)
    (color : (↥s) → (↥s) → (↥s) → Turn)
    (c : Turn) (anchor : Point 2) (k : ℕ) : Prop :=
  ∃ f : Fin k ↪ ↥s,
    (∀ (i j : Fin k), i < j →
      SukRegionLT outerLeft outerRight (f i) (f j)) ∧
    (∀ (i j l : Fin k), i < j → j < l →
      color (f i) (f j) (f l) = c ∧
      InConvexPosition {anchor, (f i).1, (f j).1, (f l).1})

private structure SukRegionVertex (s : Finset (Point 2)) where
  val : ↥s
  deriving DecidableEq, Fintype

private def sukRegionVertexEquiv (s : Finset (Point 2)) :
    SukRegionVertex s ≃ ↥s where
  toFun p := p.val
  invFun p := ⟨p⟩
  left_inv p := by cases p; rfl
  right_inv _ := rfl

@[reducible] private def sukRegionVertexPartialOrder
    (outerLeft outerRight : Point 2) (s : Finset (Point 2))
    (hside : ∀ p ∈ s, 0 < orientation outerLeft outerRight p)
    (hgp : InGeneralPosition (insert outerLeft (insert outerRight s))) :
    PartialOrder (SukRegionVertex s) where
  le p q := SukRegionLE outerLeft outerRight p.val q.val
  lt p q := SukRegionLT outerLeft outerRight p.val q.val
  le_refl p := sukRegionLE_refl outerLeft outerRight p.val
  le_trans p q r := sukRegionLE_trans outerLeft outerRight
    p.val q.val r.val
  le_antisymm p q hpq hqp := by
    have hval := (sukRegionPartialOrder outerLeft outerRight s hside hgp).le_antisymm
      p.val q.val hpq hqp
    cases p
    cases q
    cases hval
    rfl
  lt_iff_le_not_ge _ _ := Iff.rfl

@[reducible] private def sukRegionVertexLinearOrder
    (outerLeft outerRight : Point 2) (s : Finset (Point 2))
    (hside : ∀ p ∈ s, 0 < orientation outerLeft outerRight p)
    (hgp : InGeneralPosition (insert outerLeft (insert outerRight s)))
    (hchain : ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s → p ≠ q →
      SukRegionLE outerLeft outerRight p q ∨
        SukRegionLE outerLeft outerRight q p) :
    LinearOrder (SukRegionVertex s) where
  __ := sukRegionVertexPartialOrder outerLeft outerRight s hside hgp
  le_total p q := by
    by_cases hpq : p = q
    · subst q
      exact Or.inl (sukRegionLE_refl outerLeft outerRight p.val)
    · have hpqValue : (p.val : Point 2) ≠ (q.val : Point 2) := by
        intro h
        apply hpq
        have hval : p.val = q.val := Subtype.ext h
        cases p
        cases q
        cases hval
        rfl
      exact hchain p.val.property q.val.property hpqValue
  toDecidableLE := Classical.decRel _

/-- Transitivity propagates a consecutive monochromatic word to all ordered
triples of the same word. -/
private theorem allColor_of_consecutive
    {s : Finset (Point 2)} {outerLeft outerRight : Point 2}
    {color : (↥s) → (↥s) → (↥s) → Turn} {c : Turn} {n : ℕ}
    (f : Fin n → SukRegionVertex s)
    (horder : ∀ ⦃i j : Fin n⦄, i < j →
      SukRegionLT outerLeft outerRight (f i).val (f j).val)
    (htransitive :
      SukRegionTransitiveTwoColoring outerLeft outerRight color)
    (hlocal : ∀ (i j k : Fin n), (hij : i < j) → (hjk : j < k) →
      j.val = i.val + 1 → k.val = j.val + 1 →
        color (f i).val (f j).val (f k).val = c) :
    ∀ (i j k : Fin n), i < j → j < k →
      color (f i).val (f j).val (f k).val = c := by
  have aux : ∀ span : ℕ, ∀ (i j k : Fin n), k.val - i.val = span →
      (hij : i < j) → (hjk : j < k) →
      color (f i).val (f j).val (f k).val = c := by
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
          have hfirst : color (f i).val (f j).val (f m).val = c :=
            ih (m.val - i.val) (by dsimp [m]; omega)
              i j m rfl hij hjm
          have hsecond : color (f j).val (f m).val (f k).val = c :=
            ih (k.val - j.val) (by omega)
              j m k rfl hjm hmk
          exact (htransitive (f i).val (f j).val (f m).val (f k).val
            (horder hij) (horder hjm) (horder hmk)
            c hfirst hsecond).1
      · let m : Fin n := ⟨j.val - 1, by omega⟩
        have him : i < m := by
          change i.val < j.val - 1
          omega
        have hmj : m < j := by
          change j.val - 1 < j.val
          omega
        have hfirst : color (f i).val (f m).val (f j).val = c :=
          ih (j.val - i.val) (by omega)
            i m j rfl him hmj
        have hsecond : color (f m).val (f j).val (f k).val = c :=
          ih (k.val - m.val) (by dsimp [m]; omega)
            m j k rfl hmj hjk
        exact (htransitive (f i).val (f m).val (f j).val (f k).val
          (horder him) (horder hmj) (horder hjk)
          c hfirst hsecond).2
  intro i j k hij hjk
  exact aux (k.val - i.val) i j k rfl hij hjk

private theorem anchoredColorChain_of_hasNChain
    {s : Finset (Point 2)} {outerLeft outerRight anchor : Point 2}
    {color : (↥s) → (↥s) → (↥s) → Turn} {c : Turn} {k : ℕ}
    [LinearOrder (SukRegionVertex s)]
    (hstrict : ∀ ⦃p q : SukRegionVertex s⦄, p < q →
      SukRegionLT outerLeft outerRight p.val q.val)
    (htransitive :
      SukRegionTransitiveTwoColoring outerLeft outerRight color)
    (hanchor : ∀ (p q r : ↥s), SukRegionLT outerLeft outerRight p q →
      SukRegionLT outerLeft outerRight q r → color p q r = c →
        InConvexPosition {anchor, p.1, q.1, r.1})
    (h : CupCap.HasNChain
      (fun p q r : SukRegionVertex s ↦ color p.val q.val r.val)
      c k (Finset.univ : Finset (SukRegionVertex s))) :
    SukRegionHasAnchoredColorChain outerLeft outerRight color c anchor k := by
  obtain ⟨l, hchain, hlen, _⟩ := h
  subst k
  let f : Fin l.length ↪o SukRegionVertex s :=
    OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
  let g : Fin l.length ↪ ↥s :=
    f.toEmbedding.trans (sukRegionVertexEquiv s).toEmbedding
  have hlocal : ∀ (i j k : Fin l.length), (hij : i < j) → (hjk : j < k) →
      j.val = i.val + 1 → k.val = j.val + 1 →
        color (f i).val (f j).val (f k).val = c := by
    intro i j k hij hjk hijSucc hjkSucc
    have hi : i.val + 2 < l.length := by omega
    have hturn := CupCap.consecutive'_getElem hchain.2 i.val hi
    simpa [f, hijSucc, hjkSucc] using hturn
  have hall : ∀ (i j k : Fin l.length), i < j → j < k →
      color (f i).val (f j).val (f k).val = c :=
    allColor_of_consecutive f
      (fun {_ _} hij ↦ hstrict (f.strictMono hij)) htransitive hlocal
  refine ⟨g, ?_, ?_⟩
  · intro i j hij
    change SukRegionLT outerLeft outerRight (f i).val (f j).val
    exact hstrict (f.strictMono hij)
  · intro i j k hij hjk
    have hijRegion := hstrict (f.strictMono hij)
    have hjkRegion := hstrict (f.strictMono hjk)
    have hcolor := hall i j k hij hjk
    change color (f i).val (f j).val (f k).val = c ∧
      InConvexPosition {anchor, (f i).val.1, (f j).val.1, (f k).val.1}
    exact ⟨hcolor, hanchor (f i).val (f j).val (f k).val
      hijRegion hjkRegion hcolor⟩

/-- The exact finite transitive two-color cup/cap alternative on one total
`SukRegionLE` chain. -/
theorem sukRegionChain_twoColor_cup_or_cap
    (outerLeft rightAnchor leftAnchor outerRight : Point 2)
    (s : Finset (Point 2))
    (hside : ∀ p ∈ s, 0 < orientation outerLeft outerRight p)
    (hgp : InGeneralPosition
      (insert outerLeft
        (insert rightAnchor (insert leftAnchor (insert outerRight s)))))
    (hchain : ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s → p ≠ q →
      SukRegionLE outerLeft outerRight p q ∨
        SukRegionLE outerLeft outerRight q p)
    (color : (↥s) → (↥s) → (↥s) → Turn)
    (htransitive :
      SukRegionTransitiveTwoColoring outerLeft outerRight color)
    (hsemantics : SukRegionTwoColorSemantics
      rightAnchor leftAnchor outerLeft outerRight color)
    (rightSize leftSize : ℕ)
    (hrightSize : 2 ≤ rightSize) (hleftSize : 2 ≤ leftSize)
    (hcard : Nat.choose (rightSize + leftSize - 4) (rightSize - 2) <
      s.card) :
    SukRegionHasAnchoredColorChain outerLeft outerRight color
        Turn.right rightAnchor rightSize ∨
      SukRegionHasAnchoredColorChain outerLeft outerRight color
        Turn.left leftAnchor leftSize := by
  have hgpOrder :
      InGeneralPosition (insert outerLeft (insert outerRight s)) := by
    apply hgp.mono
    intro p hp
    simp only [Finset.mem_insert] at hp ⊢
    rcases hp with rfl | rfl | hp
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hp)))
  letI : LinearOrder (SukRegionVertex s) :=
    sukRegionVertexLinearOrder outerLeft outerRight s hside hgpOrder hchain
  have hstrict : ∀ ⦃p q : SukRegionVertex s⦄, p < q →
      SukRegionLT outerLeft outerRight p.val q.val := by
    intro p q hpq
    change SukRegionLT outerLeft outerRight p.val q.val at hpq
    exact hpq
  let regionColor : SukRegionVertex s → SukRegionVertex s →
      SukRegionVertex s → Turn :=
    fun p q r ↦ color p.val q.val r.val
  have hsum : (rightSize - 2) + (leftSize - 2) =
      rightSize + leftSize - 4 := by omega
  have hvertexCard :
      (Finset.univ : Finset (SukRegionVertex s)).card = s.card := by
    change Fintype.card (SukRegionVertex s) = s.card
    simpa using Fintype.card_congr (sukRegionVertexEquiv s)
  have hrecurrenceCard :
      Nat.choose ((rightSize - 2) + (leftSize - 2)) (rightSize - 2) <
        (Finset.univ : Finset (SukRegionVertex s)).card := by
    rw [hsum, hvertexCard]
    exact hcard
  have halt := CupCap.cup_cap regionColor (rightSize - 2) (leftSize - 2)
    (Finset.univ : Finset (SukRegionVertex s)) hrecurrenceCard
  rcases halt with hright | hleft
  · left
    have hrightLength : rightSize - 2 + 2 = rightSize := by omega
    have hright' : CupCap.HasNChain
        (fun p q r : SukRegionVertex s ↦ color p.val q.val r.val)
        Turn.right rightSize
        (Finset.univ : Finset (SukRegionVertex s)) := by
      simpa only [regionColor, hrightLength] using hright
    apply anchoredColorChain_of_hasNChain hstrict htransitive _ hright'
    intro p q r hpq hqr hcolor
    exact ((hsemantics p q r hpq hqr).1).mp hcolor
  · right
    have hleftLength : leftSize - 2 + 2 = leftSize := by omega
    have hleft' : CupCap.HasNChain
        (fun p q r : SukRegionVertex s ↦ color p.val q.val r.val)
        Turn.left leftSize
        (Finset.univ : Finset (SukRegionVertex s)) := by
      simpa only [regionColor, hleftLength] using hleft
    apply anchoredColorChain_of_hasNChain hstrict htransitive _ hleft'
    intro p q r hpq hqr hcolor
    exact ((hsemantics p q r hpq hqr).2).mp hcolor

/-- Source-level adjacent chain pools before the two anchor-extended caps have
been selected.  No certificate or mixed-convexity conclusion is a field. -/
structure SukAdjacentChainPools
    (x0 x1 x2 x3 x4 : Point 2)
    (leftPool rightPool : Finset (Point 2)) : Prop where
  anchorsCap : SukFiveCapAnchors x0 x1 x2 x3 x4
  disjoint : Disjoint leftPool rightPool
  generalPosition : InGeneralPosition
    (insert x0 (insert x1
      (insert x2 (insert x3 (insert x4 (leftPool ∪ rightPool))))))
  leftRegion : ∀ ⦃p⦄, p ∈ leftPool → p ∈ SukSupportRegion x0 x1 x2 x3
  rightRegion : ∀ ⦃p⦄, p ∈ rightPool → p ∈ SukSupportRegion x1 x2 x3 x4
  leftChain : ∀ ⦃p⦄, p ∈ leftPool → ∀ ⦃q⦄, q ∈ leftPool → p ≠ q →
    SukRegionLE x0 x3 p q ∨ SukRegionLE x0 x3 q p
  rightChain : ∀ ⦃p⦄, p ∈ rightPool → ∀ ⦃q⦄, q ∈ rightPool → p ≠ q →
    SukRegionLE x1 x4 p q ∨ SukRegionLE x1 x4 q p

/-- The exact open global producer: select two subsets of prescribed sizes
whose common-anchor extensions are convex. -/
def SukGlobalAdjacentChainSelection
    (x2 : Point 2) (leftPool rightPool : Finset (Point 2))
    (leftSize rightSize : ℕ) : Prop :=
  ∃ left right : Finset (Point 2),
    left ⊆ leftPool ∧ right ⊆ rightPool ∧
    left.card = leftSize ∧ right.card = rightSize ∧
    InConvexPosition (insert x2 left) ∧
    InConvexPosition (insert x2 right)

/-- A source-level global selection feeds the existing adjacent-region
certificate and hence the mixed convex-union theorem. -/
theorem sukGlobalAdjacentChainSelection_toCertificate
    (x0 x1 x2 x3 x4 : Point 2)
    (leftPool rightPool : Finset (Point 2))
    (leftSize rightSize : ℕ)
    (hpools : SukAdjacentChainPools
      x0 x1 x2 x3 x4 leftPool rightPool)
    (hselection : SukGlobalAdjacentChainSelection
      x2 leftPool rightPool leftSize rightSize) :
    ∃ left right : Finset (Point 2),
      left ⊆ leftPool ∧ right ⊆ rightPool ∧
      left.card = leftSize ∧ right.card = rightSize ∧
      SukAdjacentRegionCertificate x2 left right ∧
      InConvexPosition (left ∪ right) := by
  rcases hselection with
    ⟨left, right, hleftSubset, hrightSubset, hleftCard, hrightCard,
      hleftCap, hrightCap⟩
  have hgeneralPosition : InGeneralPosition
      (insert x0 (insert x1
        (insert x2 (insert x3 (insert x4 (left ∪ right)))))) := by
    apply hpools.generalPosition.mono
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_union] at hp ⊢
    rcases hp with rfl | rfl | rfl | rfl | rfl | hp
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hp.elim (fun h ↦ Or.inl (hleftSubset h))
          (fun h ↦ Or.inr (hrightSubset h)))))))
  let hdata : SukAdjacentSupportData x0 x1 x2 x3 x4 left right := {
    anchorsCap := hpools.anchorsCap
    disjoint := hpools.disjoint.mono hleftSubset hrightSubset
    generalPosition := hgeneralPosition
    leftRegion := by
      intro p hp
      exact hpools.leftRegion (hleftSubset hp)
    rightRegion := by
      intro p hp
      exact hpools.rightRegion (hrightSubset hp)
    leftChain := by
      intro p hp q hq hpq
      exact hpools.leftChain (hleftSubset hp) (hleftSubset hq) hpq
    rightChain := by
      intro p hp q hq hpq
      exact hpools.rightChain (hrightSubset hp) (hrightSubset hq) hpq
    leftCap := hleftCap
    rightCap := hrightCap
  }
  let hcertificate := hdata.toCertificate
  exact ⟨left, right, hleftSubset, hrightSubset, hleftCard, hrightCard,
    hcertificate, hcertificate.inConvexPosition_union⟩

end

end ErdosSzekeres

end
