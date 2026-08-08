module

public import ErdosSzekeres.StructuralChargingNextState578Reservoir

@[expose] public section

/-!
# Threshold-frontier extraction in the `(5,7,8)` reservoir

The ordered-cap tree recurrence is unavailable in an open singleton-lower
state.  The surviving tree reduction descends to an internal node whose
support still reaches the 23-vertex density threshold but whose two children
do not.  Density supplies a four-cap somewhere in that node support, and the
parent singleton-root obstruction makes its span cover the root cut.

The extracted cap is not claimed to cross the threshold node's children.
That missing local interaction is the next mathematical obstruction.
-/

namespace ErdosSzekeres

namespace DecompositionTree

/-- An internal tree node whose support reaches `threshold` while neither
child support does. -/
structure ThresholdFrontierNode {n : ℕ} {χ : TripleColoring n}
    {support : Finset (Fin n)} (tree : DecompositionTree χ support)
    (threshold : ℕ) where
  path : List Bool
  node : DecompositionSplit χ
  lookup : tree.splitAtPath path = some node
  support_large : threshold ≤ (node.lower ∪ node.upper).card
  lower_small : node.lower.card < threshold
  upper_small : node.upper.card < threshold

/-- Every node reached by a valid path has support contained in the root
support. -/
theorem splitAtPath_support_subset
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node) :
    node.lower ∪ node.upper ⊆ support := by
  induction tree generalizing path node with
  | singleton i =>
      cases path <;> simp [splitAtPath] at hlookup
  | @split lower upper lowerTree upperTree deep ihlower ihupper =>
      cases path with
      | nil =>
          simp only [splitAtPath, Option.some.injEq] at hlookup
          subst node
          exact Finset.Subset.rfl
      | cons direction path =>
          cases direction
          · have hchild : node.lower ∪ node.upper ⊆ lower :=
              ihlower (by simpa [splitAtPath] using hlookup)
            exact hchild.trans Finset.subset_union_left
          · have hchild : node.lower ∪ node.upper ⊆ upper :=
              ihupper (by simpa [splitAtPath] using hlookup)
            exact hchild.trans Finset.subset_union_right

/-- A node reached by a valid path carries its own decomposability proof. -/
theorem splitAtPath_isDecomposableOn
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node) :
    IsDecomposableOn χ (node.lower ∪ node.upper) := by
  induction tree generalizing path node with
  | singleton i =>
      cases path <;> simp [splitAtPath] at hlookup
  | @split lower upper lowerTree upperTree deep ihlower ihupper =>
      cases path with
      | nil =>
          simp only [splitAtPath, Option.some.injEq] at hlookup
          subst node
          exact .split lowerTree.toIsDecomposableOn
            upperTree.toIsDecomposableOn deep
      | cons direction path =>
          cases direction
          · exact ihlower (by simpa [splitAtPath] using hlookup)
          · exact ihupper (by simpa [splitAtPath] using hlookup)

/-- Every tree whose support reaches a threshold of at least two contains a
threshold-frontier node.  Descent chooses the lower qualifying child first;
no uniqueness claim is needed. -/
theorem exists_thresholdFrontierNode
    {n threshold : ℕ} {χ : TripleColoring n}
    {support : Finset (Fin n)} (tree : DecompositionTree χ support)
    (hthreshold : 2 ≤ threshold) (hsupport : threshold ≤ support.card) :
    Nonempty (ThresholdFrontierNode tree threshold) := by
  induction tree with
  | singleton i =>
      simp at hsupport
      omega
  | @split lower upper lowerTree upperTree deep ihlower ihupper =>
      by_cases hlower : threshold ≤ lower.card
      · obtain ⟨frontier⟩ := ihlower hlower
        exact ⟨{
          path := false :: frontier.path
          node := frontier.node
          lookup := by simpa [splitAtPath] using frontier.lookup
          support_large := frontier.support_large
          lower_small := frontier.lower_small
          upper_small := frontier.upper_small
        }⟩
      by_cases hupper : threshold ≤ upper.card
      · obtain ⟨frontier⟩ := ihupper hupper
        exact ⟨{
          path := true :: frontier.path
          node := frontier.node
          lookup := by simpa [splitAtPath] using frontier.lookup
          support_large := frontier.support_large
          lower_small := frontier.lower_small
          upper_small := frontier.upper_small
        }⟩
      · exact ⟨{
          path := []
          node := ⟨lower, upper, deep⟩
          lookup := by simp [splitAtPath]
          support_large := hsupport
          lower_small := by
            show lower.card < threshold
            omega
          upper_small := by
            show upper.card < threshold
            omega
        }⟩

end DecompositionTree

/-- The exact positive payload surviving threshold descent at `(5,7,8)`:
a dense internal node with children of size at most 22 and a four-cap in its
support whose interval straddles the original singleton root. -/
structure DenseFourCapFrontier578
    {n : ℕ} (χ : TripleColoring n) {q : Fin n}
    {upper : Finset (Fin n)} (tree : DecompositionTree χ upper) where
  path : List Bool
  node : DecompositionSplit χ
  lookup : tree.splitAtPath path = some node
  support_card_ge : 23 ≤ (node.lower ∪ node.upper).card
  lower_card_le : node.lower.card ≤ 22
  upper_card_le : node.upper.card ≤ 22
  cap : Finset (Fin n)
  cap_mem : cap ∈ capWitnesses χ (node.lower ∪ node.upper) 4
  cap_straddles_root :
    (finsetSweepInterval cap (by
      have hcard := (mem_capWitnesses.mp cap_mem).2.1
      exact Finset.card_pos.mp (by omega))).StraddlesCut q.val

/-- Every hypothetical open singleton-lower `1+32` state has a dense
threshold-frontier node.  This proves the extraction skeleton only; it does
not say that the selected cap crosses the node split. -/
theorem exists_denseFourCapFrontier_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)} (tree : DecompositionTree χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    Nonempty (DenseFourCapFrontier578 χ (q := q) tree) := by
  obtain ⟨frontier⟩ :=
    tree.exists_thresholdFrontierNode (threshold := 23) (by omega) (by omega)
  have hnodeSub :=
    tree.splitAtPath_support_subset frontier.lookup
  have hnodeDecomposable :=
    tree.splitAtPath_isDecomposableOn frontier.lookup
  obtain ⟨cap, hcapSub, hcapCard, hcapSet⟩ :=
    containsCapFour_of_decomposable_large_subset_at_578
      hnodeDecomposable frontier.support_large hnodeSub hnoCup hnoStrong
  have hcapMem :
      cap ∈ capWitnesses χ (frontier.node.lower ∪ frontier.node.upper) 4 :=
    mem_capWitnesses.mpr ⟨hcapSub, hcapCard, hcapSet⟩
  have hcapUpper : cap ∈ capWitnesses χ upper 4 :=
    mem_capWitnesses.mpr ⟨hcapSub.trans hnodeSub, hcapCard, hcapSet⟩
  exact ⟨{
    path := frontier.path
    node := frontier.node
    lookup := frontier.lookup
    support_card_ge := frontier.support_large
    lower_card_le := by
      have hsmall := frontier.lower_small
      omega
    upper_card_le := by
      have hsmall := frontier.upper_small
      omega
    cap := cap
    cap_mem := hcapMem
    cap_straddles_root :=
      hroot.root_straddles_every_upper_cap_of_no_succ_cap
        (a := 4) (by omega) hnoCap cap hcapUpper
  }⟩

namespace SweepInterval

/-- The number of integer sweep gaps between an interval's endpoints. -/
def width (interval : SweepInterval) : ℕ :=
  interval.upper - interval.lower

/-- Strict interval containment, allowing one endpoint to remain fixed. -/
def StrictlyInside (inner outer : SweepInterval) : Prop :=
  outer.lower ≤ inner.lower ∧
    inner.upper ≤ outer.upper ∧
    (outer.lower < inner.lower ∨ inner.upper < outer.upper)

/-- Strict containment decreases interval width. -/
theorem width_lt_of_strictlyInside {inner outer : SweepInterval}
    (hinner : inner.lower ≤ inner.upper)
    (houter : outer.lower ≤ outer.upper)
    (hinside : inner.StrictlyInside outer) :
    inner.width < outer.width := by
  simp only [width, StrictlyInside] at *
  omega

end SweepInterval

/-- A nonempty finite vertex set has its minimum sweep index at or before its
maximum sweep index. -/
theorem finsetSweepInterval_lower_le_upper
    {n : ℕ} {s : Finset (Fin n)} (hs : s.Nonempty) :
    (finsetSweepInterval s hs).lower ≤ (finsetSweepInterval s hs).upper := by
  change (s.min' hs).val ≤ (s.max' hs).val
  exact Finset.min'_le_max' s hs

/-- A positive-cardinality cap witness is nonempty. -/
theorem capWitness_nonempty_of_mem
    {n a : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (ha : 0 < a) (hcap : cap ∈ capWitnesses χ support a) :
    cap.Nonempty := by
  have hcard := (mem_capWitnesses.mp hcap).2.1
  exact Finset.card_pos.mp (by omega)

/-- The corrected local descent contract.  It is stated only from the
independent structural data used downstream: an explicit decomposition tree,
23-subset four-cap density, and a common sweep cut for every four-cap.  The
conclusion strictly nests the span of each cap.

Unlike a contradiction asserted under all open-root hypotheses, this contract
is not vacuously implied by `SingletonLowerCriticalGate578`; it can be tested
or refuted on any decomposable coloring carrying these three data. -/
def DenseFourCapStrictSpanDescent32_23 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n} {q : Fin n}
      {upper : Finset (Fin n)} (_tree : DecompositionTree χ upper),
    upper.card = 32 →
    (∀ subset : Finset (Fin n), subset ⊆ upper →
      subset.card = 23 → ContainsCapSet χ subset 4) →
    (∀ cap, (hcap : cap ∈ capWitnesses χ upper 4) →
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val) →
    ∀ cap, (hcap : cap ∈ capWitnesses χ upper 4) →
      ∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))

/-- The corrected descent contract is a complete contradiction consumer:
choose a four-cap of minimum span width, then apply strict descent. -/
theorem false_of_denseFourCapStrictSpanDescent32_23
    (hdescent : DenseFourCapStrictSpanDescent32_23)
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)} (tree : DecompositionTree χ upper)
    (hupperCard : upper.card = 32)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ upper →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hstraddles : ∀ cap, (hcap : cap ∈ capWitnesses χ upper 4) →
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val) :
    False := by
  obtain ⟨subset, hsubset, hsubsetCard⟩ :=
    Finset.exists_subset_card_eq (show 23 ≤ upper.card by omega)
  obtain ⟨cap₀, hcap₀Sub, hcap₀Card, hcap₀Set⟩ :=
    hdense subset hsubset hsubsetCard
  have hcap₀ : cap₀ ∈ capWitnesses χ upper 4 :=
    mem_capWitnesses.mpr
      ⟨hcap₀Sub.trans hsubset, hcap₀Card, hcap₀Set⟩
  let spanWidth (cap : Finset (Fin n))
      (hcap : cap ∈ capWitnesses χ upper 4) : ℕ :=
    (finsetSweepInterval cap
      (capWitness_nonempty_of_mem (by omega) hcap)).width
  let WidthOccurs (width : ℕ) : Prop :=
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      spanWidth cap hcap = width
  have hex : ∃ width, WidthOccurs width :=
    ⟨spanWidth cap₀ hcap₀, cap₀, hcap₀, rfl⟩
  obtain ⟨cap, hcap, hwidth⟩ := Nat.find_spec hex
  obtain ⟨inner, hinner, hinside⟩ :=
    hdescent tree hupperCard hdense hstraddles cap hcap
  have hwidthLt : spanWidth inner hinner < spanWidth cap hcap := by
    apply SweepInterval.width_lt_of_strictlyInside
    · exact finsetSweepInterval_lower_le_upper
        (capWitness_nonempty_of_mem (by omega) hinner)
    · exact finsetSweepInterval_lower_le_upper
        (capWitness_nonempty_of_mem (by omega) hcap)
    · exact hinside
  have hmin : Nat.find hex ≤ spanWidth inner hinner :=
    Nat.find_min' hex ⟨inner, hinner, rfl⟩
  rw [hwidth] at hwidthLt
  omega

/-- Specializing the independent strict-span descent contract to the compiled
dense common-cut reservoir closes the singleton-lower `(5,7,8)` gate. -/
theorem singletonLowerCriticalGate578_of_denseFourCapStrictSpanDescent
    (hdescent : DenseFourCapStrictSpanDescent32_23) :
    SingletonLowerCriticalGate578 := by
  intro n χ q upper hupper hroot hupperCard hnoCap hnoCup hnoStrong
  obtain ⟨tree⟩ := DecompositionTree.exists_of_isDecomposableOn hupper
  have hreservoir :=
    dense_straddling_cap_reservoir_at_578
      hupper hroot hnoCap hnoCup hnoStrong
  exact false_of_denseFourCapStrictSpanDescent32_23
    hdescent tree hupperCard hreservoir.1 hreservoir.2

end ErdosSzekeres

end
