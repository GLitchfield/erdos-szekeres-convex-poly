module

public import ErdosSzekeres.StructuralChargingNextState578PrivateCaps

@[expose] public section

/-!
# Whole-cap traces for the state-578 private caps

This module begins to route every vertex of a private cap, rather than only
its selected owner.  Relative to the terminal cap's path, every support
vertex is either still in the final node or has a first exit in one of the two
directions.  A vertex not covered by a lower-sibling bucket cannot have the
lower-directed kind of exit.
-/

namespace ErdosSzekeres

namespace DecompositionTree

/-- The first split on a fixed path where a whole moving set no longer fits in
the selected child.  Unlike `FirstExitAlongPath`, this records the shallowest
escape among all vertices of the set. -/
inductive FirstSetEscapeAlongPath {n : ℕ} {χ : TripleColoring n}
    (moving : Finset (Fin n)) :
    {support : Finset (Fin n)} → DecompositionTree χ support →
      List Bool → Bool → Prop
  | lowerHere {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      (hmoving : moving ⊆ lower ∪ upper) (hnotLower : ¬moving ⊆ lower) :
      FirstSetEscapeAlongPath moving (.split lowerTree upperTree deep)
        (false :: suffix) false
  | upperHere {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      (hmoving : moving ⊆ lower ∪ upper) (hnotUpper : ¬moving ⊆ upper) :
      FirstSetEscapeAlongPath moving (.split lowerTree upperTree deep)
        (true :: suffix) true
  | lowerBelow {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      {escapeDirection : Bool} (hmoving : moving ⊆ lower)
      (below : FirstSetEscapeAlongPath moving lowerTree suffix escapeDirection) :
      FirstSetEscapeAlongPath moving (.split lowerTree upperTree deep)
        (false :: suffix) escapeDirection
  | upperBelow {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) {suffix : List Bool}
      {escapeDirection : Bool} (hmoving : moving ⊆ upper)
      (below : FirstSetEscapeAlongPath moving upperTree suffix escapeDirection) :
      FirstSetEscapeAlongPath moving (.split lowerTree upperTree deep)
        (true :: suffix) escapeDirection

/-- A set in the root support either survives wholly inside the final node or
has a well-defined first whole-set escape along the path. -/
theorem subset_node_or_exists_firstSetEscapeAlongPath
    {n : ℕ} {χ : TripleColoring n} {support moving : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (hmovingSupport : moving ⊆ support) :
    moving ⊆ node.lower ∪ node.upper ∨
      ∃ escapeDirection,
        FirstSetEscapeAlongPath moving tree path escapeDirection := by
  induction tree generalizing path node with
  | singleton i =>
      cases path <;> simp [splitAtPath] at hlookup
  | @split lower upper lowerTree upperTree deep ihLower ihUpper =>
      cases path with
      | nil =>
          simp only [splitAtPath, Option.some.injEq] at hlookup
          subst node
          exact Or.inl hmovingSupport
      | cons direction suffix =>
          cases direction
          · have hchildLookup : lowerTree.splitAtPath suffix = some node := by
              simpa [splitAtPath] using hlookup
            by_cases hmovingLower : moving ⊆ lower
            · rcases ihLower hchildLookup hmovingLower with
                hmovingNode | hescape
              · exact Or.inl hmovingNode
              · obtain ⟨escapeDirection, hescape⟩ := hescape
                exact Or.inr ⟨escapeDirection,
                  .lowerBelow lowerTree upperTree deep hmovingLower hescape⟩
            · exact Or.inr ⟨false,
                .lowerHere lowerTree upperTree deep
                  hmovingSupport hmovingLower⟩
          · have hchildLookup : upperTree.splitAtPath suffix = some node := by
              simpa [splitAtPath] using hlookup
            by_cases hmovingUpper : moving ⊆ upper
            · rcases ihUpper hchildLookup hmovingUpper with
                hmovingNode | hescape
              · exact Or.inl hmovingNode
              · obtain ⟨escapeDirection, hescape⟩ := hescape
                exact Or.inr ⟨escapeDirection,
                  .upperBelow lowerTree upperTree deep hmovingUpper hescape⟩
            · exact Or.inr ⟨true,
                .upperHere lowerTree upperTree deep
                  hmovingSupport hmovingUpper⟩

/-- If the first whole-set escape of a four-cap occurs while the followed path
selects the lower child, the two interior cap vertices collide in that step's
lower-sibling bucket. -/
theorem FirstSetEscapeAlongPath.exists_two_in_lowerSiblingBucket_of_cap
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {escapeDirection : Bool}
    (hescape : FirstSetEscapeAlongPath cap tree path escapeDirection)
    (hcap : cap ∈ capWitnesses χ support 4)
    (hdirection : escapeDirection = false) :
    ∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
      ∃ y ∈ cap, ∃ z ∈ cap,
        y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket := by
  induction hescape with
  | lowerHere lowerTree upperTree deep hcapSupport hnotLower =>
      let hcard := (mem_capWitnesses.mp hcap).2.1
      let c := cap.orderEmbOfFin hcard
      have hshape := capFour_deepSplit_lower_subset_endpoints
        deep hcap hnotLower
      change c 1 ∈ _ ∧ c 2 ∈ _ ∧ _ at hshape
      refine ⟨upperTree.supportSet,
        by simp [lowerSiblingSupportsAlongPath], c 1,
        cap.orderEmbOfFin_mem hcard 1, c 2,
        cap.orderEmbOfFin_mem hcard 2, ?_, hshape.1, hshape.2.1⟩
      exact ne_of_lt (c.strictMono (by decide))
  | upperHere => exact Bool.noConfusion hdirection
  | lowerBelow lowerTree upperTree deep hcapLower below ih =>
      have hcapChild : cap ∈ capWitnesses χ lowerTree.supportSet 4 :=
        mem_capWitnesses.mpr ⟨hcapLower, (mem_capWitnesses.mp hcap).2⟩
      obtain ⟨bucket, hbucket, y, hyCap, z, hzCap, hyz,
          hyBucket, hzBucket⟩ := ih hcapChild hdirection
      exact ⟨bucket,
        by simp [lowerSiblingSupportsAlongPath, hbucket],
        y, hyCap, z, hzCap, hyz, hyBucket, hzBucket⟩
  | upperBelow lowerTree upperTree deep hcapUpper below ih =>
      have hcapChild : cap ∈ capWitnesses χ upperTree.supportSet 4 :=
        mem_capWitnesses.mpr ⟨hcapUpper, (mem_capWitnesses.mp hcap).2⟩
      simpa [lowerSiblingSupportsAlongPath] using ih hcapChild hdirection

/-- A four-cap either survives wholly in the final node, first escapes at an
upper-directed step, or already has a two-vertex lower-sibling collision. -/
theorem subset_node_or_true_firstSetEscape_or_bucketCollision
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (hcap : cap ∈ capWitnesses χ support 4) :
    cap ⊆ node.lower ∪ node.upper ∨
      FirstSetEscapeAlongPath cap tree path true ∨
      (∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
        ∃ y ∈ cap, ∃ z ∈ cap,
          y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket) := by
  rcases subset_node_or_exists_firstSetEscapeAlongPath tree hlookup
      (mem_capWitnesses.mp hcap).1 with hnode | hescape
  · exact Or.inl hnode
  · obtain ⟨direction, hescape⟩ := hescape
    cases direction
    · exact Or.inr (Or.inr
        (hescape.exists_two_in_lowerSiblingBucket_of_cap hcap rfl))
    · exact Or.inr (Or.inl hescape)

/-- Every support vertex is either still in the node reached by a cap path or
has a first exit in exactly one of the two possible directions. -/
theorem mem_node_or_false_or_true_firstExitAlongPath
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ} {x : Fin n}
    (hlookup : tree.splitAtPath path = some node)
    (hcapNode : cap ⊆ node.lower ∪ node.upper)
    (hxSupport : x ∈ support) :
    x ∈ node.lower ∪ node.upper ∨
      FirstExitAlongPath cap x tree path false ∨
      FirstExitAlongPath cap x tree path true := by
  by_cases hxNode : x ∈ node.lower ∪ node.upper
  · exact Or.inl hxNode
  · obtain ⟨direction, hexit⟩ :=
      exists_firstExitAlongPath tree hlookup hcapNode hxSupport hxNode
    cases direction
    · exact Or.inr (Or.inl hexit)
    · exact Or.inr (Or.inr hexit)

/-- A vertex with a first exit along a path is outside the split reached at
the end of that path. -/
theorem FirstExitAlongPath.not_mem_splitAtPath
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {x : Fin n} {exitDirection : Bool}
    (hexit : FirstExitAlongPath cap x tree path exitDirection)
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node) :
    x ∉ node.lower ∪ node.upper := by
  induction hexit with
  | lowerHere lowerTree upperTree deep hcap hx =>
      intro hxNode
      have hxLower : x ∈ lowerTree.supportSet :=
        lowerTree.splitAtPath_support_subset
          (by simpa [splitAtPath] using hlookup) hxNode
      exact (Finset.disjoint_left.mp deep.disjoint) hxLower hx
  | upperHere lowerTree upperTree deep hcap hx =>
      intro hxNode
      have hxUpper : x ∈ upperTree.supportSet :=
        upperTree.splitAtPath_support_subset
          (by simpa [splitAtPath] using hlookup) hxNode
      exact (Finset.disjoint_left.mp deep.disjoint) hx hxUpper
  | lowerBelow lowerTree upperTree deep hcap hx below ih =>
      exact ih (by simpa [splitAtPath] using hlookup)
  | upperBelow lowerTree upperTree deep hcap hx below ih =>
      exact ih (by simpa [splitAtPath] using hlookup)

/-- A support vertex with no lower-sibling bucket either remains in the final
node or first leaves while the cap branch follows an upper child. -/
theorem uncovered_internal_or_true_firstExitAlongPath
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {node : DecompositionSplit χ} {x : Fin n}
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : IsLowestSeparatingPath cap tree path)
    (hxSupport : x ∈ support)
    (huncovered : ¬∃ bucket,
      bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧ x ∈ bucket) :
    x ∈ node.lower ∪ node.upper ∨
      FirstExitAlongPath cap x tree path true := by
  have hcapNode := (hallocated.splitAtPath_spec hlookup).1
  rcases mem_node_or_false_or_true_firstExitAlongPath
      tree hlookup hcapNode hxSupport with hxNode | hxFalse | hxTrue
  · exact Or.inl hxNode
  · obtain ⟨bucket, hbucket, hxBucket⟩ :=
      hxFalse.mem_lowerSiblingSupportsAlongPath rfl
    exact False.elim (huncovered ⟨bucket, hbucket, hxBucket⟩)
  · exact Or.inr hxTrue

end DecompositionTree

/-- Every external private cap either has a lower-sibling bucket collision or
contains a non-owner whose path trace goes in the direction opposite to the
owner, unless that non-owner survives inside the final node. -/
theorem IsPrivateFourCapAssignment.privateCap_nonowner_internal_or_trueExit_or_bucketCollision
    {n : ℕ} {χ : TripleColoring n}
    {support terminal marked : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {node : DecompositionSplit χ}
    {capFor : Fin n → Finset (Fin n)}
    (hassign : IsPrivateFourCapAssignment χ support terminal marked capFor)
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : DecompositionTree.IsLowestSeparatingPath terminal tree path)
    {x : Fin n} (hxMarked : x ∈ marked)
    (hexit : DecompositionTree.FirstExitAlongPath terminal x tree path false) :
    (∃ y ∈ capFor x, y ≠ x ∧
      (y ∈ node.lower ∪ node.upper ∨
        DecompositionTree.FirstExitAlongPath terminal y tree path true)) ∨
    (∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
      ∃ y ∈ capFor x, ∃ z ∈ capFor x,
        y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket) := by
  rcases hassign.privateCap_nonowner_uncovered_or_bucketCollision
      hxMarked hexit with huncovered | hcollision
  · left
    obtain ⟨y, hyCap, hyx, hyUncovered⟩ := huncovered
    have hySupport : y ∈ support :=
      (mem_capWitnesses.mp (hassign x hxMarked).1).1 hyCap
    exact ⟨y, hyCap, hyx,
      DecompositionTree.uncovered_internal_or_true_firstExitAlongPath
        hlookup hallocated hySupport hyUncovered⟩
  · exact Or.inr hcollision

/-- A private cap whose owner exits in the lower direction cannot survive in
the final node.  Its shallowest whole-cap event is therefore either an
upper-directed escape or a certified lower-sibling bucket collision. -/
theorem IsPrivateFourCapAssignment.privateCap_true_firstSetEscape_or_bucketCollision
    {n : ℕ} {χ : TripleColoring n}
    {support terminal marked : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {node : DecompositionSplit χ}
    {capFor : Fin n → Finset (Fin n)}
    (hassign : IsPrivateFourCapAssignment χ support terminal marked capFor)
    (hlookup : tree.splitAtPath path = some node)
    {x : Fin n} (hxMarked : x ∈ marked)
    (hexit : DecompositionTree.FirstExitAlongPath
      terminal x tree path false) :
    DecompositionTree.FirstSetEscapeAlongPath (capFor x) tree path true ∨
      (∃ bucket, bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
        ∃ y ∈ capFor x, ∃ z ∈ capFor x,
          y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket) := by
  have hcap := (hassign x hxMarked).1
  rcases DecompositionTree.subset_node_or_true_firstSetEscape_or_bucketCollision
      tree hlookup hcap with hnode | htrue | hcollision
  · exact False.elim
      (hexit.not_mem_splitAtPath hlookup (hnode (hassign x hxMarked).2.2.1))
  · exact Or.inl htrue
  · exact Or.inr hcollision

/-- The six-tail package after whole-cap tracing.  Either three owners remain
in the lowest terminal node, or at least three external owners have private
caps whose shallowest event is a true escape or a bucket collision. -/
def HasThreePrivateCapTraceOwners {n : ℕ} (χ : TripleColoring n)
    (support terminal tails : Finset (Fin n))
    (tree : DecompositionTree χ support) (path : List Bool)
    (node : DecompositionSplit χ) : Prop :=
  ∃ transversal, ∃ capFor : Fin n → Finset (Fin n),
    transversal ⊆ tails ∧
    HitsEveryFourCapDisjointFrom χ support terminal transversal ∧
    IsPrivateFourCapAssignment χ support terminal transversal capFor ∧
    Set.InjOn capFor (transversal : Set (Fin n)) ∧
    6 ≤ (transversal.image capFor).card ∧
    (3 ≤ (transversal ∩ (node.lower ∪ node.upper)).card ∨
      (3 ≤ (transversal \ (node.lower ∪ node.upper)).card ∧
        ∀ x ∈ transversal \ (node.lower ∪ node.upper),
          DecompositionTree.FirstSetEscapeAlongPath
              (capFor x) tree path true ∨
            ∃ bucket,
              bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧
              ∃ y ∈ capFor x, ∃ z ∈ capFor x,
                y ≠ z ∧ y ∈ bucket ∧ z ∈ bucket))

/-- Whole-cap tracing upgrades the six routed private owners to the exact
three-owner global residual. -/
theorem HasSixPrivateRoutedTailTransversal.hasThreePrivateCapTraceOwners
    {n : ℕ} {χ : TripleColoring n}
    {support terminal tails : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (h : HasSixPrivateRoutedTailTransversal χ support terminal tails
      tree path node) :
    HasThreePrivateCapTraceOwners χ support terminal tails tree path node := by
  obtain ⟨transversal, htransversalTails, hcard, hhits,
      hprivate, hroutes⟩ := h
  obtain ⟨capFor, hassignment, hinjective, himageCard⟩ :=
    exists_card_preserving_privateFourCapAssignment hprivate
  refine ⟨transversal, capFor, htransversalTails, hhits, hassignment,
    hinjective, by omega, ?_⟩
  rcases three_le_inter_or_sdiff_of_six_le_card transversal
      (node.lower ∪ node.upper) hcard with hinternal | hexternal
  · exact Or.inl hinternal
  · right
    refine ⟨hexternal, ?_⟩
    intro x hxExternal
    have hxData := Finset.mem_sdiff.mp hxExternal
    rcases hroutes x hxData.1 with hxInternal | hxExit
    · exact False.elim (hxData.2 hxInternal)
    · exact hassignment.privateCap_true_firstSetEscape_or_bucketCollision
        hlookup hxData.1 hxExit

/-- Density defeats any proposed shared core of at most five vertices as a
transversal of all residual four-caps: another residual cap avoids it.  This
is the strongest density-only repair of the shared-core obstruction. -/
theorem exists_residualFourCap_disjoint_from_small_avoidance_at_32_23
    {n : ℕ} {χ : TripleColoring n}
    {support fixed avoid : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hfixed : fixed ∈ capWitnesses χ support 4)
    (havoidSub : avoid ⊆ support)
    (hfixedAvoid : Disjoint fixed avoid)
    (havoidCard : avoid.card ≤ 5)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4) :
    ∃ secondary,
      secondary ∈ capWitnesses χ support 4 ∧
      Disjoint fixed secondary ∧ Disjoint avoid secondary := by
  by_contra hnone
  push Not at hnone
  have hlarge := six_le_residualCapTransversal_at_32_23
    hsupportCard hfixed havoidSub hfixedAvoid hdense (by
      intro secondary hsecondary hfixedSecondary
      exact hnone secondary hsecondary hfixedSecondary)
  omega

/-- The actual singleton-lower state-578 obstruction carries the global
three-owner whole-cap trace residual. -/
theorem exists_terminalFourCap_threePrivateCapTraceOwners_at_578
    {n : ℕ} {χ : TripleColoring n} {q : Fin n}
    {upper : Finset (Fin n)}
    (hupper : IsDecomposableOn χ upper)
    (hroot : HasDeepBelowSplit χ {q} upper)
    (hupperCard : upper.card = 32)
    (hstate558 : DecomposableStateUpper 5 5 8)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 5)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 7)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 8) :
    ∃ cap, ∃ hcap : cap ∈ capWitnesses χ upper 4,
      (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ upper 4,
        (finsetSweepInterval inner
          (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
        (finsetSweepInterval cap
          (capWitness_nonempty_of_mem (by omega) hcap))) ∧
      (finsetSweepInterval cap
        (capWitness_nonempty_of_mem (by omega) hcap)).StraddlesCut q.val ∧
      let tails := (upper \ openSweepSpanVertices upper cap
        (capWitness_nonempty_of_mem (by omega) hcap)) \ cap
      9 ≤ tails.card ∧
      ∃ tree : DecompositionTree χ upper,
        ∃ path : List Bool, ∃ node : DecompositionSplit χ,
        tree.splitAtPath path = some node ∧
        DecompositionTree.IsLowestSeparatingPath cap tree path ∧
        (((cap ∩ node.lower).card = 1 ∧
            (cap ∩ node.upper).card = 3 ∧
            ¬ContainsCupSet χ node.lower 5 ∧ node.lower.card ≤ 20) ∨
          ((cap ∩ node.lower).card = 2 ∧
            (cap ∩ node.upper).card = 2 ∧
            ¬ContainsCupSet χ node.lower 6)) ∧
        HasThreePrivateCapTraceOwners χ upper cap tails tree path node := by
  obtain ⟨cap, hcap, hterminal, hstraddles, htail,
      tree, path, node, hlookup, hallocated, halternative, hrouted⟩ :=
    exists_terminalFourCap_sixPrivateRoutedTailTransversal_at_578
      hupper hroot hupperCard hstate558 hnoCap hnoCup hnoStrong
  exact ⟨cap, hcap, hterminal, hstraddles, htail,
    tree, path, node, hlookup, hallocated, halternative,
    hrouted.hasThreePrivateCapTraceOwners hlookup⟩

end ErdosSzekeres

end
