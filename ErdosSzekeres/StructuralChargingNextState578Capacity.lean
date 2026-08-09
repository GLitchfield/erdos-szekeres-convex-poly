module

public import ErdosSzekeres.StructuralChargingNextState578TwoTwo

@[expose] public section

/-!
# Terminal-tail capacity infrastructure at state `(5,7,8)`

This file turns lower-directed first-exit addresses into disjoint sibling
reservoirs and reconnects the terminal cap to secondary caps supplied by the
global `32/23` density theorem.
-/

namespace ErdosSzekeres
namespace DecompositionTree

/-- Recover the support index of an explicit decomposition tree as data. -/
def supportSet {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (_tree : DecompositionTree χ support) : Finset (Fin n) := support

/-- The upper-sibling supports encountered at lower (`false`) steps along a
tree path.  These are exactly the possible reservoirs for lower-directed
first exits from that path. -/
def lowerSiblingSupportsAlongPath {n : ℕ} {χ : TripleColoring n} :
    {support : Finset (Fin n)} → DecompositionTree χ support →
      List Bool → List (Finset (Fin n))
  | _, .singleton _, _ => []
  | _, .split _ _ _, [] => []
  | _, .split lowerTree upperTree _, false :: path =>
      upperTree.supportSet :: lowerSiblingSupportsAlongPath lowerTree path
  | _, .split _lowerTree upperTree _, true :: path =>
      lowerSiblingSupportsAlongPath upperTree path

/-- Every sibling support collected along a path is contained in the root
support. -/
theorem lowerSiblingSupportsAlongPath_subset
    {n : ℕ} {χ : TripleColoring n} {support sibling : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool}
    (hsibling : sibling ∈ tree.lowerSiblingSupportsAlongPath path) :
    sibling ⊆ support := by
  induction tree generalizing path with
  | singleton i => simp [lowerSiblingSupportsAlongPath] at hsibling
  | @split lower upper lowerTree upperTree deep ihLower ihUpper =>
      cases path with
      | nil => simp [lowerSiblingSupportsAlongPath] at hsibling
      | cons direction path =>
          cases direction
          · simp only [lowerSiblingSupportsAlongPath, List.mem_cons] at hsibling
            rcases hsibling with rfl | hsibling
            · exact Finset.subset_union_right
            · exact (ihLower hsibling).trans Finset.subset_union_left
          · exact (ihUpper (by
              simpa [lowerSiblingSupportsAlongPath] using hsibling)).trans
                Finset.subset_union_right

/-- Upper siblings at distinct lower steps of one path are pairwise disjoint.
This is the tree-conservation fact needed before any capacity estimate can be
attached to first-exit addresses. -/
theorem lowerSiblingSupportsAlongPath_pairwise_disjoint
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    (tree : DecompositionTree χ support) (path : List Bool) :
    (tree.lowerSiblingSupportsAlongPath path).Pairwise
      (fun first second ↦ Disjoint first second) := by
  induction tree generalizing path with
  | singleton i => simp [lowerSiblingSupportsAlongPath]
  | @split lower upper lowerTree upperTree deep ihLower ihUpper =>
      cases path with
      | nil => simp [lowerSiblingSupportsAlongPath]
      | cons direction path =>
          cases direction
          · simp only [lowerSiblingSupportsAlongPath, List.pairwise_cons]
            constructor
            · intro sibling hsibling
              have hsub : sibling ⊆ lower :=
                lowerTree.lowerSiblingSupportsAlongPath_subset hsibling
              rw [Finset.disjoint_left]
              intro x hxUpper hxSibling
              exact (Finset.disjoint_left.mp deep.disjoint)
                (hsub hxSibling) hxUpper
            · exact ihLower path
          · simpa [lowerSiblingSupportsAlongPath] using ihUpper path

/-- In a pairwise-disjoint list of finite sets, a vertex determines at most
one member containing it. -/
theorem eq_of_mem_of_mem_of_mem_pairwiseDisjoint
    {n : ℕ} {sets : List (Finset (Fin n))} {first second : Finset (Fin n)}
    {x : Fin n} (hpairwise : sets.Pairwise (fun left right ↦ Disjoint left right))
    (hfirst : first ∈ sets) (hsecond : second ∈ sets)
    (hxFirst : x ∈ first) (hxSecond : x ∈ second) : first = second := by
  induction sets with
  | nil => simp at hfirst
  | cons head tail ih =>
      simp only [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hfirst hsecond
      rcases hfirst with rfl | hfirst
      · rcases hsecond with rfl | hsecond
        · rfl
        · exact False.elim
            ((Finset.disjoint_left.mp (hpairwise.1 second hsecond))
              hxFirst hxSecond)
      · rcases hsecond with rfl | hsecond
        · exact False.elim
            ((Finset.disjoint_left.mp (hpairwise.1 first hfirst))
              hxSecond hxFirst)
        · exact ih hpairwise.2 hfirst hsecond

/-- The sibling bucket containing a lower-first-exit vertex is unique. -/
theorem lowerSiblingSupportsAlongPath_unique_of_mem
    {n : ℕ} {χ : TripleColoring n} {support first second : Finset (Fin n)}
    (tree : DecompositionTree χ support) {path : List Bool} {x : Fin n}
    (hfirst : first ∈ tree.lowerSiblingSupportsAlongPath path)
    (hsecond : second ∈ tree.lowerSiblingSupportsAlongPath path)
    (hxFirst : x ∈ first) (hxSecond : x ∈ second) : first = second := by
  exact eq_of_mem_of_mem_of_mem_pairwiseDisjoint
    (tree.lowerSiblingSupportsAlongPath_pairwise_disjoint path)
    hfirst hsecond hxFirst hxSecond

/-- A lower-directed first exit places its vertex in one of the disjoint
upper-sibling supports collected along the cap path. -/
theorem FirstExitAlongPath.mem_lowerSiblingSupportsAlongPath
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool} {x : Fin n}
    {exitDirection : Bool}
    (hexit : FirstExitAlongPath cap x tree path exitDirection)
    (hdirection : exitDirection = false) :
    ∃ sibling,
      sibling ∈ tree.lowerSiblingSupportsAlongPath path ∧ x ∈ sibling := by
  induction hexit with
  | lowerHere lowerTree upperTree deep hcap hx =>
      refine ⟨upperTree.supportSet, by simp [lowerSiblingSupportsAlongPath], ?_⟩
      simpa [supportSet] using hx
  | upperHere => exact Bool.noConfusion hdirection
  | lowerBelow lowerTree upperTree deep hcap hx below ih =>
      obtain ⟨sibling, hsibling, hxSibling⟩ := ih hdirection
      exact ⟨sibling, by simp [lowerSiblingSupportsAlongPath, hsibling], hxSibling⟩
  | upperBelow lowerTree upperTree deep hcap hx below ih =>
      simpa [lowerSiblingSupportsAlongPath] using ih hdirection

/-- In a list of exit buckets, the bucket containing `shallow` occurs before
a bucket containing `deeper`. -/
inductive VertexBucketBefore {n : ℕ} (shallow deeper : Fin n) :
    List (Finset (Fin n)) → Prop
  | here {head : Finset (Fin n)} {tail : List (Finset (Fin n))}
      (hshallow : shallow ∈ head)
      (hdeeper : ∃ bucket, bucket ∈ tail ∧ deeper ∈ bucket) :
      VertexBucketBefore shallow deeper (head :: tail)
  | later {head : Finset (Fin n)} {tail : List (Finset (Fin n))}
      (below : VertexBucketBefore shallow deeper tail) :
      VertexBucketBefore shallow deeper (head :: tail)

/-- The earlier vertex in `VertexBucketBefore` occurs in some listed bucket. -/
theorem VertexBucketBefore.shallow_mem
    {n : ℕ} {shallow deeper : Fin n} {sets : List (Finset (Fin n))}
    (hbefore : VertexBucketBefore shallow deeper sets) :
    ∃ bucket, bucket ∈ sets ∧ shallow ∈ bucket := by
  induction hbefore with
  | here hshallow hdeeper => exact ⟨_, by simp, hshallow⟩
  | later below ih =>
      obtain ⟨bucket, hbucket, hshallow⟩ := ih
      exact ⟨bucket, by simp [hbucket], hshallow⟩

/-- The later vertex in `VertexBucketBefore` occurs in some listed bucket. -/
theorem VertexBucketBefore.deeper_mem
    {n : ℕ} {shallow deeper : Fin n} {sets : List (Finset (Fin n))}
    (hbefore : VertexBucketBefore shallow deeper sets) :
    ∃ bucket, bucket ∈ sets ∧ deeper ∈ bucket := by
  induction hbefore with
  | here hshallow hdeeper =>
      obtain ⟨bucket, hbucket, hdeep⟩ := hdeeper
      exact ⟨bucket, by simp [hbucket], hdeep⟩
  | later below ih =>
      obtain ⟨bucket, hbucket, hdeep⟩ := ih
      exact ⟨bucket, by simp [hbucket], hdeep⟩

/-- Strict bucket order is asymmetric when the listed buckets are pairwise
disjoint. -/
theorem VertexBucketBefore.not_reverse_of_pairwiseDisjoint
    {n : ℕ} {shallow deeper : Fin n} {sets : List (Finset (Fin n))}
    (hbefore : VertexBucketBefore shallow deeper sets)
    (hpairwise : sets.Pairwise (fun first second ↦ Disjoint first second)) :
    ¬VertexBucketBefore deeper shallow sets := by
  induction hbefore with
  | @here head tail hshallow hdeeper =>
      intro hreverse
      simp only [List.pairwise_cons] at hpairwise
      cases hreverse with
      | here hdeepHead hshallowTail =>
          obtain ⟨bucket, hbucket, hdeep⟩ := hdeeper
          exact (Finset.disjoint_left.mp (hpairwise.1 bucket hbucket))
            hdeepHead hdeep
      | later below =>
          obtain ⟨bucket, hbucket, hshallowBucket⟩ := below.deeper_mem
          exact (Finset.disjoint_left.mp (hpairwise.1 bucket hbucket))
            hshallow hshallowBucket
  | @later head tail below ih =>
      intro hreverse
      simp only [List.pairwise_cons] at hpairwise
      cases hreverse with
      | here hdeepHead hshallowTail =>
          obtain ⟨bucket, hbucket, hdeepBucket⟩ := below.deeper_mem
          exact (Finset.disjoint_left.mp (hpairwise.1 bucket hbucket))
            hdeepHead hdeepBucket
      | later reverseBelow => exact ih hpairwise.2 reverseBelow

/-- In a list of disjoint exit buckets, the bucket containing `shallow`
occurs before buckets containing each of the two deeper vertices. -/
inductive VertexBucketBeforeTwo {n : ℕ}
    (shallow deeper₁ deeper₂ : Fin n) :
    List (Finset (Fin n)) → Prop
  | here {head : Finset (Fin n)} {tail : List (Finset (Fin n))}
      (hshallow : shallow ∈ head)
      (hdeeper₁ : ∃ bucket, bucket ∈ tail ∧ deeper₁ ∈ bucket)
      (hdeeper₂ : ∃ bucket, bucket ∈ tail ∧ deeper₂ ∈ bucket) :
      VertexBucketBeforeTwo shallow deeper₁ deeper₂ (head :: tail)
  | later {head : Finset (Fin n)} {tail : List (Finset (Fin n))}
      (below : VertexBucketBeforeTwo shallow deeper₁ deeper₂ tail) :
      VertexBucketBeforeTwo shallow deeper₁ deeper₂ (head :: tail)

/-- Forget the second deeper vertex from an ordered two-vertex comparison. -/
theorem VertexBucketBeforeTwo.before_deeper₁
    {n : ℕ} {shallow deeper₁ deeper₂ : Fin n}
    {sets : List (Finset (Fin n))}
    (hbefore : VertexBucketBeforeTwo shallow deeper₁ deeper₂ sets) :
    VertexBucketBefore shallow deeper₁ sets := by
  induction hbefore with
  | here hshallow hdeeper₁ hdeeper₂ => exact .here hshallow hdeeper₁
  | later below ih => exact .later ih

/-- Forget the first deeper vertex from an ordered two-vertex comparison. -/
theorem VertexBucketBeforeTwo.before_deeper₂
    {n : ℕ} {shallow deeper₁ deeper₂ : Fin n}
    {sets : List (Finset (Fin n))}
    (hbefore : VertexBucketBeforeTwo shallow deeper₁ deeper₂ sets) :
    VertexBucketBefore shallow deeper₂ sets := by
  induction hbefore with
  | here hshallow hdeeper₁ hdeeper₂ => exact .here hshallow hdeeper₂
  | later below ih => exact .later ih

/-- Three vertices occupying three different buckets have a unique candidate
for the shallowest bucket. -/
theorem vertexBucketBeforeTwo_trichotomy
    {n : ℕ} {first second third : Fin n}
    {sets : List (Finset (Fin n))}
    (hfirst : ∃ bucket, bucket ∈ sets ∧ first ∈ bucket)
    (hsecond : ∃ bucket, bucket ∈ sets ∧ second ∈ bucket)
    (hthird : ∃ bucket, bucket ∈ sets ∧ third ∈ bucket)
    (hfirstSecond : ∀ bucket ∈ sets,
      ¬(first ∈ bucket ∧ second ∈ bucket))
    (hfirstThird : ∀ bucket ∈ sets,
      ¬(first ∈ bucket ∧ third ∈ bucket))
    (hsecondThird : ∀ bucket ∈ sets,
      ¬(second ∈ bucket ∧ third ∈ bucket)) :
    VertexBucketBeforeTwo first second third sets ∨
      VertexBucketBeforeTwo second first third sets ∨
      VertexBucketBeforeTwo third first second sets := by
  induction sets with
  | nil => simp at hfirst
  | cons head tail ih =>
      have firstTail (hnot : first ∉ head) :
          ∃ bucket, bucket ∈ tail ∧ first ∈ bucket := by
        obtain ⟨bucket, hbucket, hmem⟩ := hfirst
        rcases (List.mem_cons.mp hbucket) with rfl | hbucket
        · exact False.elim (hnot hmem)
        · exact ⟨bucket, hbucket, hmem⟩
      have secondTail (hnot : second ∉ head) :
          ∃ bucket, bucket ∈ tail ∧ second ∈ bucket := by
        obtain ⟨bucket, hbucket, hmem⟩ := hsecond
        rcases (List.mem_cons.mp hbucket) with rfl | hbucket
        · exact False.elim (hnot hmem)
        · exact ⟨bucket, hbucket, hmem⟩
      have thirdTail (hnot : third ∉ head) :
          ∃ bucket, bucket ∈ tail ∧ third ∈ bucket := by
        obtain ⟨bucket, hbucket, hmem⟩ := hthird
        rcases (List.mem_cons.mp hbucket) with rfl | hbucket
        · exact False.elim (hnot hmem)
        · exact ⟨bucket, hbucket, hmem⟩
      by_cases hf : first ∈ head
      · have hs : second ∉ head := by
          intro hs
          exact hfirstSecond head (by simp) ⟨hf, hs⟩
        have ht : third ∉ head := by
          intro ht
          exact hfirstThird head (by simp) ⟨hf, ht⟩
        exact Or.inl (.here hf (secondTail hs) (thirdTail ht))
      · by_cases hs : second ∈ head
        · have ht : third ∉ head := by
            intro ht
            exact hsecondThird head (by simp) ⟨hs, ht⟩
          exact Or.inr (Or.inl (.here hs (firstTail hf) (thirdTail ht)))
        · by_cases ht : third ∈ head
          · exact Or.inr (Or.inr (.here ht (firstTail hf) (secondTail hs)))
          · rcases ih (firstTail hf) (secondTail hs) (thirdTail ht)
                (fun bucket hbucket ↦ hfirstSecond bucket (by simp [hbucket]))
                (fun bucket hbucket ↦ hfirstThird bucket (by simp [hbucket]))
                (fun bucket hbucket ↦ hsecondThird bucket (by simp [hbucket])) with
              h | h | h
            · exact Or.inl (.later h)
            · exact Or.inr (Or.inl (.later h))
            · exact Or.inr (Or.inr (.later h))

/-- Distinct witness buckets in a pairwise-disjoint list prevent their marked
vertices from cohabiting any listed bucket. -/
theorem not_mem_same_bucket_of_distinct_witnessBuckets
    {n : ℕ} {first second : Fin n} {firstBucket secondBucket : Finset (Fin n)}
    {sets : List (Finset (Fin n))}
    (hpairwise : sets.Pairwise (fun left right ↦ Disjoint left right))
    (hfirstBucket : firstBucket ∈ sets)
    (hsecondBucket : secondBucket ∈ sets)
    (hdistinct : firstBucket ≠ secondBucket)
    (hfirst : first ∈ firstBucket) (hsecond : second ∈ secondBucket) :
    ∀ bucket ∈ sets, ¬(first ∈ bucket ∧ second ∈ bucket) := by
  intro bucket hbucket hboth
  have hbucketFirst : bucket = firstBucket :=
    eq_of_mem_of_mem_of_mem_pairwiseDisjoint hpairwise
      hbucket hfirstBucket hboth.1 hfirst
  have hbucketSecond : bucket = secondBucket :=
    eq_of_mem_of_mem_of_mem_pairwiseDisjoint hpairwise
      hbucket hsecondBucket hboth.2 hsecond
  exact hdistinct (hbucketFirst.symm.trans hbucketSecond)
/-- One lower-first-exit bucket occurs before the buckets containing two
deeper vertices along the same path.  The decisive constructor remembers the
split at the shallower exit; the other constructors transport the relation
through a common path prefix. -/
inductive LowerExitBeforeTwoAlongPath {n : ℕ} {χ : TripleColoring n}
    (shallow deeper₁ deeper₂ : Fin n) :
    {support : Finset (Fin n)} → DecompositionTree χ support →
      List Bool → Prop
  | here {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper)
      (suffix : List Bool)
      (hshallow : shallow ∈ upper)
      (hdeeper₁ : ∃ sibling,
        sibling ∈ lowerTree.lowerSiblingSupportsAlongPath suffix ∧
          deeper₁ ∈ sibling)
      (hdeeper₂ : ∃ sibling,
        sibling ∈ lowerTree.lowerSiblingSupportsAlongPath suffix ∧
          deeper₂ ∈ sibling) :
      LowerExitBeforeTwoAlongPath shallow deeper₁ deeper₂
        (.split lowerTree upperTree deep) (false :: suffix)
  | lowerBelow {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper)
      (suffix : List Bool)
      (below : LowerExitBeforeTwoAlongPath shallow deeper₁ deeper₂
        lowerTree suffix) :
      LowerExitBeforeTwoAlongPath shallow deeper₁ deeper₂
        (.split lowerTree upperTree deep) (false :: suffix)
  | upperBelow {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper)
      (suffix : List Bool)
      (below : LowerExitBeforeTwoAlongPath shallow deeper₁ deeper₂
        upperTree suffix) :
      LowerExitBeforeTwoAlongPath shallow deeper₁ deeper₂
        (.split lowerTree upperTree deep) (true :: suffix)

/-- Ordered membership in the explicit lower-sibling bucket list exposes the
decisive decomposition split witnessing the corresponding exit order. -/
theorem lowerExitBeforeTwoAlongPath_of_vertexBucketBeforeTwo
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {shallow deeper₁ deeper₂ : Fin n}
    (tree : DecompositionTree χ support) {path : List Bool}
    (horder : VertexBucketBeforeTwo shallow deeper₁ deeper₂
      (tree.lowerSiblingSupportsAlongPath path)) :
    LowerExitBeforeTwoAlongPath shallow deeper₁ deeper₂ tree path := by
  induction tree generalizing path with
  | singleton i =>
      change VertexBucketBeforeTwo shallow deeper₁ deeper₂ [] at horder
      cases horder
  | @split lower upper lowerTree upperTree deep ihLower ihUpper =>
      cases path with
      | nil =>
          change VertexBucketBeforeTwo shallow deeper₁ deeper₂ [] at horder
          cases horder
      | cons direction suffix =>
          cases direction
          · change VertexBucketBeforeTwo shallow deeper₁ deeper₂
              (upperTree.supportSet ::
                lowerTree.lowerSiblingSupportsAlongPath suffix) at horder
            cases horder with
            | here hshallow hdeeper₁ hdeeper₂ =>
                exact .here lowerTree upperTree deep suffix
                  hshallow hdeeper₁ hdeeper₂
            | later below =>
                exact .lowerBelow lowerTree upperTree deep suffix
                  (ihLower below)
          · exact .upperBelow lowerTree upperTree deep suffix
              (ihUpper (by
                simpa [lowerSiblingSupportsAlongPath] using horder))

/-- If the first sweep vertex exits before the other two at lower-directed
steps, their triple is left-colored. -/
theorem LowerExitBeforeTwoAlongPath.color_eq_left_of_shallow_first
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {i j k : Fin n} {tree : DecompositionTree χ support}
    {path : List Bool}
    (hexits : LowerExitBeforeTwoAlongPath i j k tree path)
    (hij : i < j) (hjk : j < k) : χ ⟨i, j, k, hij, hjk⟩ = .left := by
  induction hexits with
  | here lowerTree upperTree deep suffix hiUpper hjExit hkExit =>
      obtain ⟨jSibling, hjSibling, hjMem⟩ := hjExit
      obtain ⟨kSibling, hkSibling, hkMem⟩ := hkExit
      have hjLower :=
        lowerTree.lowerSiblingSupportsAlongPath_subset hjSibling hjMem
      have hkLower :=
        lowerTree.lowerSiblingSupportsAlongPath_subset hkSibling hkMem
      have hcross := deep.crossing ⟨i, j, k, hij, hjk⟩
        (Finset.mem_union_right _ hiUpper)
        (Finset.mem_union_left _ hjLower)
        (Finset.mem_union_left _ hkLower)
        (by
          rintro ⟨hiLower, -, -⟩
          exact (Finset.disjoint_left.mp deep.disjoint) hiLower hiUpper)
        (by
          rintro ⟨-, hjUpper, -⟩
          exact (Finset.disjoint_left.mp deep.disjoint) hjLower hjUpper)
      simpa [hjLower] using hcross
  | lowerBelow lowerTree upperTree deep suffix below ih => exact ih
  | upperBelow lowerTree upperTree deep suffix below ih => exact ih

/-- If the middle sweep vertex exits before the other two at lower-directed
steps, their triple is right-colored. -/
theorem LowerExitBeforeTwoAlongPath.color_eq_right_of_shallow_middle
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {i j k : Fin n} {tree : DecompositionTree χ support}
    {path : List Bool}
    (hexits : LowerExitBeforeTwoAlongPath j i k tree path)
    (hij : i < j) (hjk : j < k) : χ ⟨i, j, k, hij, hjk⟩ = .right := by
  induction hexits with
  | here lowerTree upperTree deep suffix hjUpper hiExit hkExit =>
      obtain ⟨iSibling, hiSibling, hiMem⟩ := hiExit
      obtain ⟨kSibling, hkSibling, hkMem⟩ := hkExit
      have hiLower :=
        lowerTree.lowerSiblingSupportsAlongPath_subset hiSibling hiMem
      have hkLower :=
        lowerTree.lowerSiblingSupportsAlongPath_subset hkSibling hkMem
      have hjNotLower : j ∉ lowerTree.supportSet := by
        intro hjLower
        exact (Finset.disjoint_left.mp deep.disjoint) hjLower hjUpper
      have hcross := deep.crossing ⟨i, j, k, hij, hjk⟩
        (Finset.mem_union_left _ hiLower)
        (Finset.mem_union_right _ hjUpper)
        (Finset.mem_union_left _ hkLower)
        (by
          rintro ⟨-, hjLower, -⟩
          exact hjNotLower hjLower)
        (by
          rintro ⟨hiUpper, -, -⟩
          exact (Finset.disjoint_left.mp deep.disjoint) hiLower hiUpper)
      change χ ⟨i, j, k, hij, hjk⟩ =
        if j ∈ lowerTree.supportSet then .left else .right at hcross
      rw [if_neg hjNotLower] at hcross
      exact hcross
  | lowerBelow lowerTree upperTree deep suffix below ih => exact ih
  | upperBelow lowerTree upperTree deep suffix below ih => exact ih

/-- If the last sweep vertex exits before the other two at lower-directed
steps, their triple is left-colored. -/
theorem LowerExitBeforeTwoAlongPath.color_eq_left_of_shallow_last
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {i j k : Fin n} {tree : DecompositionTree χ support}
    {path : List Bool}
    (hexits : LowerExitBeforeTwoAlongPath k i j tree path)
    (hij : i < j) (hjk : j < k) : χ ⟨i, j, k, hij, hjk⟩ = .left := by
  induction hexits with
  | here lowerTree upperTree deep suffix hkUpper hiExit hjExit =>
      obtain ⟨iSibling, hiSibling, hiMem⟩ := hiExit
      obtain ⟨jSibling, hjSibling, hjMem⟩ := hjExit
      have hiLower :=
        lowerTree.lowerSiblingSupportsAlongPath_subset hiSibling hiMem
      have hjLower :=
        lowerTree.lowerSiblingSupportsAlongPath_subset hjSibling hjMem
      have hcross := deep.crossing ⟨i, j, k, hij, hjk⟩
        (Finset.mem_union_left _ hiLower)
        (Finset.mem_union_left _ hjLower)
        (Finset.mem_union_right _ hkUpper)
        (by
          rintro ⟨-, -, hkLower⟩
          exact (Finset.disjoint_left.mp deep.disjoint) hkLower hkUpper)
        (by
          rintro ⟨hiUpper, -, -⟩
          exact (Finset.disjoint_left.mp deep.disjoint) hiLower hiUpper)
      simpa [hjLower] using hcross
  | lowerBelow lowerTree upperTree deep suffix below ih => exact ih
  | upperBelow lowerTree upperTree deep suffix below ih => exact ih

/-- Four sweep-ordered vertices whose two consecutive triples each occupy
distinct lower-exit buckets cannot form a cap.  The first middle vertex would
have to exit before the second, while the final triple forces the reverse. -/
theorem not_isCapSet_four_of_adjacent_distinct_lowerSiblingBuckets
    {n : ℕ} {χ : TripleColoring n} {support : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {i j k l : Fin n} {iBucket jBucket kBucket lBucket : Finset (Fin n)}
    (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hiBucket : iBucket ∈ tree.lowerSiblingSupportsAlongPath path)
    (hjBucket : jBucket ∈ tree.lowerSiblingSupportsAlongPath path)
    (hkBucket : kBucket ∈ tree.lowerSiblingSupportsAlongPath path)
    (hlBucket : lBucket ∈ tree.lowerSiblingSupportsAlongPath path)
    (hi : i ∈ iBucket) (hj : j ∈ jBucket)
    (hk : k ∈ kBucket) (hl : l ∈ lBucket)
    (hijBucket : iBucket ≠ jBucket)
    (hikBucket : iBucket ≠ kBucket)
    (hjkBucket : jBucket ≠ kBucket)
    (hjlBucket : jBucket ≠ lBucket)
    (hklBucket : kBucket ≠ lBucket) :
    ¬IsCapSet χ {i, j, k, l} := by
  intro hcap
  let sets := tree.lowerSiblingSupportsAlongPath path
  have hpairwise : sets.Pairwise
      (fun first second ↦ Disjoint first second) :=
    tree.lowerSiblingSupportsAlongPath_pairwise_disjoint path
  have noSame {first second : Fin n}
      {firstBucket secondBucket : Finset (Fin n)}
      (hfirstBucket : firstBucket ∈ sets)
      (hsecondBucket : secondBucket ∈ sets)
      (hdistinct : firstBucket ≠ secondBucket)
      (hfirst : first ∈ firstBucket) (hsecond : second ∈ secondBucket) :
      ∀ bucket ∈ sets, ¬(first ∈ bucket ∧ second ∈ bucket) :=
    not_mem_same_bucket_of_distinct_witnessBuckets hpairwise
      hfirstBucket hsecondBucket hdistinct hfirst hsecond
  have hiMem : ∃ bucket, bucket ∈ sets ∧ i ∈ bucket :=
    ⟨iBucket, hiBucket, hi⟩
  have hjMem : ∃ bucket, bucket ∈ sets ∧ j ∈ bucket :=
    ⟨jBucket, hjBucket, hj⟩
  have hkMem : ∃ bucket, bucket ∈ sets ∧ k ∈ bucket :=
    ⟨kBucket, hkBucket, hk⟩
  have hlMem : ∃ bucket, bucket ∈ sets ∧ l ∈ bucket :=
    ⟨lBucket, hlBucket, hl⟩
  have hrightIJK : χ ⟨i, j, k, hij, hjk⟩ = .right :=
    hcap _ (by simp) (by simp) (by simp)
  have hjBeforeIK : VertexBucketBeforeTwo j i k sets := by
    rcases vertexBucketBeforeTwo_trichotomy hiMem hjMem hkMem
        (noSame hiBucket hjBucket hijBucket hi hj)
        (noSame hiBucket hkBucket hikBucket hi hk)
        (noSame hjBucket hkBucket hjkBucket hj hk) with
      hiBefore | hjBefore | hkBefore
    · have hleft :=
        lowerExitBeforeTwoAlongPath_of_vertexBucketBeforeTwo tree hiBefore
      have hcolor := hleft.color_eq_left_of_shallow_first hij hjk
      rw [hrightIJK] at hcolor
      exact Turn.noConfusion hcolor
    · exact hjBefore
    · have hleft :=
        lowerExitBeforeTwoAlongPath_of_vertexBucketBeforeTwo tree hkBefore
      have hcolor := hleft.color_eq_left_of_shallow_last hij hjk
      rw [hrightIJK] at hcolor
      exact Turn.noConfusion hcolor
  have hrightJKL : χ ⟨j, k, l, hjk, hkl⟩ = .right :=
    hcap _ (by simp) (by simp) (by simp)
  have hkBeforeJL : VertexBucketBeforeTwo k j l sets := by
    rcases vertexBucketBeforeTwo_trichotomy hjMem hkMem hlMem
        (noSame hjBucket hkBucket hjkBucket hj hk)
        (noSame hjBucket hlBucket hjlBucket hj hl)
        (noSame hkBucket hlBucket hklBucket hk hl) with
      hjBefore | hkBefore | hlBefore
    · have hleft :=
        lowerExitBeforeTwoAlongPath_of_vertexBucketBeforeTwo tree hjBefore
      have hcolor := hleft.color_eq_left_of_shallow_first hjk hkl
      rw [hrightJKL] at hcolor
      exact Turn.noConfusion hcolor
    · exact hkBefore
    · have hleft :=
        lowerExitBeforeTwoAlongPath_of_vertexBucketBeforeTwo tree hlBefore
      have hcolor := hleft.color_eq_left_of_shallow_last hjk hkl
      rw [hrightJKL] at hcolor
      exact Turn.noConfusion hcolor
  exact (hjBeforeIK.before_deeper₂.not_reverse_of_pairwiseDisjoint hpairwise)
    hkBeforeJL.before_deeper₁

/-- A cap whose vertices all lie in lower-exit buckets has at most three
vertices if every such bucket contains at most one cap vertex.  This is the
first numerical consumer of the ordered first-exit invariant. -/
theorem IsCapSet.card_le_three_of_lowerSiblingBucket_fibers
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    (tree : DecompositionTree χ support) (path : List Bool)
    (hcap : IsCapSet χ cap)
    (hcovered : ∀ x ∈ cap, ∃ bucket,
      bucket ∈ tree.lowerSiblingSupportsAlongPath path ∧ x ∈ bucket)
    (hfiber : ∀ bucket ∈ tree.lowerSiblingSupportsAlongPath path,
      ∀ {x y}, x ∈ cap → y ∈ cap →
        x ∈ bucket → y ∈ bucket → x = y) :
    cap.card ≤ 3 := by
  by_contra hcard
  have hfourLe : 4 ≤ cap.card := by omega
  obtain ⟨four, hfourSub, hfourCard⟩ :=
    Finset.exists_subset_card_eq hfourLe
  let c := four.orderEmbOfFin hfourCard
  have hcMem (r : Fin 4) : c r ∈ cap :=
    hfourSub (four.orderEmbOfFin_mem hfourCard r)
  obtain ⟨iBucket, hiBucket, hi⟩ := hcovered (c 0) (hcMem 0)
  obtain ⟨jBucket, hjBucket, hj⟩ := hcovered (c 1) (hcMem 1)
  obtain ⟨kBucket, hkBucket, hk⟩ := hcovered (c 2) (hcMem 2)
  obtain ⟨lBucket, hlBucket, hl⟩ := hcovered (c 3) (hcMem 3)
  have bucket_ne {a b : Fin 4} {aBucket bBucket : Finset (Fin n)}
      (haBucket : aBucket ∈ tree.lowerSiblingSupportsAlongPath path)
      (hbBucket : bBucket ∈ tree.lowerSiblingSupportsAlongPath path)
      (ha : c a ∈ aBucket) (hb : c b ∈ bBucket)
      (hab : c a ≠ c b) : aBucket ≠ bBucket := by
    intro heq
    subst bBucket
    exact hab (hfiber aBucket haBucket (hcMem a) (hcMem b) ha hb)
  have h01 : c 0 < c 1 := c.strictMono (by decide)
  have h12 : c 1 < c 2 := c.strictMono (by decide)
  have h23 : c 2 < c 3 := c.strictMono (by decide)
  have hnotCap := not_isCapSet_four_of_adjacent_distinct_lowerSiblingBuckets
    h01 h12 h23 hiBucket hjBucket hkBucket hlBucket hi hj hk hl
    (bucket_ne hiBucket hjBucket hi hj (ne_of_lt h01))
    (bucket_ne hiBucket hkBucket hi hk (ne_of_lt (h01.trans h12)))
    (bucket_ne hjBucket hkBucket hj hk (ne_of_lt h12))
    (bucket_ne hjBucket hlBucket hj hl (ne_of_lt (h12.trans h23)))
    (bucket_ne hkBucket hlBucket hk hl (ne_of_lt h23))
  apply hnotCap
  exact FinsetPolygon.IsCapSet.mono hcap (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · exact hcMem 0
    · exact hcMem 1
    · exact hcMem 2
    · exact hcMem 3)

end DecompositionTree

/-- A terminal-tail vertex is routed either into the lowest cap node or to a
lower-directed first exit above that node. -/
def IsInternalOrLowerFirstExit {n : ℕ} {χ : TripleColoring n}
    {support : Finset (Fin n)} (cap : Finset (Fin n)) (x : Fin n)
    (tree : DecompositionTree χ support) (path : List Bool)
    (node : DecompositionSplit χ) : Prop :=
  x ∈ node.lower ∪ node.upper ∨
    DecompositionTree.FirstExitAlongPath cap x tree path false

/-- Two disjoint secondary cap witnesses marked by distinct terminal tails and
routed relative to one lowest cap node. -/
def HasTwoRoutedSecondaryCaps {n : ℕ} (χ : TripleColoring n)
    (support terminal tails : Finset (Fin n))
    (tree : DecompositionTree χ support) (path : List Bool)
    (node : DecompositionSplit χ) : Prop :=
  ∃ first second x y,
    first ∈ capWitnesses χ support 4 ∧
    second ∈ capWitnesses χ support 4 ∧
    Disjoint terminal first ∧ Disjoint terminal second ∧
    Disjoint first second ∧
    x ∈ first ∧ x ∈ tails ∧ y ∈ second ∧ y ∈ tails ∧ x ≠ y ∧
    IsInternalOrLowerFirstExit terminal x tree path node ∧
    IsInternalOrLowerFirstExit terminal y tree path node

/-- A vertex set meeting every four-cap disjoint from a fixed four-cap. -/
def HitsEveryFourCapDisjointFrom {n : ℕ} (χ : TripleColoring n)
    (support fixed transversal : Finset (Fin n)) : Prop :=
  ∀ secondary, secondary ∈ capWitnesses χ support 4 →
    Disjoint fixed secondary → ¬Disjoint transversal secondary

/-- Six or more essential terminal tails, each with a private residual cap and
an internal-or-lower-first-exit route at the terminal cap's lowest node. -/
def HasSixPrivateRoutedTailTransversal {n : ℕ} (χ : TripleColoring n)
    (support terminal tails : Finset (Fin n))
    (tree : DecompositionTree χ support) (path : List Bool)
    (node : DecompositionSplit χ) : Prop :=
  ∃ transversal,
    transversal ⊆ tails ∧ 6 ≤ transversal.card ∧
    HitsEveryFourCapDisjointFrom χ support terminal transversal ∧
    (∀ x ∈ transversal, ∃ secondary,
      secondary ∈ capWitnesses χ support 4 ∧
      Disjoint terminal secondary ∧ x ∈ secondary ∧
      Disjoint (transversal.erase x) secondary) ∧
    ∀ x ∈ transversal,
      IsInternalOrLowerFirstExit terminal x tree path node

/-- Candidate multiplicity gate: in the target-free regime, every four-cap
disjoint from a terminal four-cap with nine outer tails uses at least two of
those tails.  A bounded counterexample below will test this exact contract. -/
def TerminalNineTailSecondaryMultiplicityGate578 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {support terminal secondary : Finset (Fin n)},
    (hterminalCap : terminal ∈ capWitnesses χ support 4) →
    (¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap))) →
    ¬ContainsCapSet χ support 5 →
    ¬ContainsCupSet χ support 7 →
    ¬ContainsStrongPolygonSet χ support 8 →
    let tails := (support \ openSweepSpanVertices support terminal
      (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal
    9 ≤ tails.card →
    secondary ∈ capWitnesses χ support 4 →
    Disjoint terminal secondary →
    2 ≤ (secondary ∩ tails).card

/-- An endpoint-bridge vertex in the root support has the internal-or-lower-
first-exit route at the cap's lowest node. -/
theorem internal_or_lowerFirstExit_of_endpointBridge
    {n : ℕ} {χ : TripleColoring n} {support cap : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {node : DecompositionSplit χ} {x : Fin n}
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : DecompositionTree.IsLowestSeparatingPath cap tree path)
    (hcapCard : cap.card = 4) (hxSupport : x ∈ support)
    (hbridge : RealizesCapFourFailureSignature χ cap hcapCard x .before ∨
      RealizesCapFourFailureSignature χ cap hcapCard x .after) :
    IsInternalOrLowerFirstExit cap x tree path node := by
  by_cases hxNode : x ∈ node.lower ∪ node.upper
  · exact Or.inl hxNode
  · exact Or.inr
      (DecompositionTree.exists_false_firstExitAlongPath_of_endpoint_bridge
        tree hlookup hallocated hcapCard hxSupport hxNode hbridge)

/-- In a `32/23` dense four-cap reservoir, any fixed four-cap can be extended
to three pairwise-disjoint four-caps while keeping the first cap fixed. -/
theorem exists_two_fourCaps_pairwiseDisjoint_from_given_at_32_23
    {n : ℕ} {χ : TripleColoring n} {support fixed : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hfixed : fixed ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4) :
    ∃ first second,
      first ∈ capWitnesses χ support 4 ∧
      second ∈ capWitnesses χ support 4 ∧
      Disjoint fixed first ∧ Disjoint fixed second ∧ Disjoint first second := by
  have hfixedData := mem_capWitnesses.mp hfixed
  let rest₁ := support \ fixed
  have hrest₁Card : rest₁.card = 28 := by
    rw [Finset.card_sdiff_of_subset hfixedData.1, hsupportCard, hfixedData.2.1]
  obtain ⟨sample₁, hsample₁Rest, hsample₁Card⟩ :=
    Finset.exists_subset_card_eq (show 23 ≤ rest₁.card by omega)
  have hsample₁Support : sample₁ ⊆ support :=
    hsample₁Rest.trans Finset.sdiff_subset
  obtain ⟨first, hfirstSample, hfirstCard, hfirstCap⟩ :=
    hdense sample₁ hsample₁Support hsample₁Card
  have hfirstRest : first ⊆ rest₁ := hfirstSample.trans hsample₁Rest
  have hfirstSupport : first ⊆ support := hfirstRest.trans Finset.sdiff_subset
  let rest₂ := rest₁ \ first
  have hrest₂Card : rest₂.card = 24 := by
    rw [Finset.card_sdiff_of_subset hfirstRest, hrest₁Card, hfirstCard]
  obtain ⟨sample₂, hsample₂Rest, hsample₂Card⟩ :=
    Finset.exists_subset_card_eq (show 23 ≤ rest₂.card by omega)
  have hsample₂Support : sample₂ ⊆ support :=
    hsample₂Rest.trans (Finset.sdiff_subset.trans Finset.sdiff_subset)
  obtain ⟨second, hsecondSample, hsecondCard, hsecondCap⟩ :=
    hdense sample₂ hsample₂Support hsample₂Card
  have hsecondRest₂ : second ⊆ rest₂ := hsecondSample.trans hsample₂Rest
  have hsecondRest₁ : second ⊆ rest₁ := hsecondRest₂.trans Finset.sdiff_subset
  have hsecondSupport : second ⊆ support :=
    hsecondRest₁.trans Finset.sdiff_subset
  have hfixedFirst : Disjoint fixed first := by
    rw [Finset.disjoint_left]
    intro x hxFixed hxFirst
    exact (Finset.mem_sdiff.mp (hfirstRest hxFirst)).2 hxFixed
  have hfixedSecond : Disjoint fixed second := by
    rw [Finset.disjoint_left]
    intro x hxFixed hxSecond
    exact (Finset.mem_sdiff.mp (hsecondRest₁ hxSecond)).2 hxFixed
  have hfirstSecond : Disjoint first second := by
    rw [Finset.disjoint_left]
    intro x hxFirst hxSecond
    exact (Finset.mem_sdiff.mp (hsecondRest₂ hxSecond)).2 hxFirst
  exact ⟨first, second,
    mem_capWitnesses.mpr ⟨hfirstSupport, hfirstCard, hfirstCap⟩,
    mem_capWitnesses.mpr ⟨hsecondSupport, hsecondCard, hsecondCap⟩,
    hfixedFirst, hfixedSecond, hfirstSecond⟩

/-- Any residual transversal meeting every four-cap disjoint from a fixed
four-cap in a `32/23` dense support has at least six vertices.  Otherwise a
23-subset survives deletion of the fixed cap and the transversal. -/
theorem six_le_residualCapTransversal_at_32_23
    {n : ℕ} {χ : TripleColoring n}
    {support fixed transversal : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hfixed : fixed ∈ capWitnesses χ support 4)
    (htransversalSub : transversal ⊆ support)
    (hfixedTransversal : Disjoint fixed transversal)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hhits : ∀ secondary, secondary ∈ capWitnesses χ support 4 →
      Disjoint fixed secondary → ¬Disjoint transversal secondary) :
    6 ≤ transversal.card := by
  by_contra hcard
  have htransversalCard : transversal.card ≤ 5 := by omega
  have hfixedData := mem_capWitnesses.mp hfixed
  let residual := support \ fixed
  have hresidualCard : residual.card = 28 := by
    rw [Finset.card_sdiff_of_subset hfixedData.1,
      hsupportCard, hfixedData.2.1]
  have htransversalResidual : transversal ⊆ residual := by
    intro x hxTransversal
    exact Finset.mem_sdiff.mpr ⟨htransversalSub hxTransversal,
      fun hxFixed ↦
        (Finset.disjoint_left.mp hfixedTransversal) hxFixed hxTransversal⟩
  let rest := residual \ transversal
  have hrestCard : 23 ≤ rest.card := by
    rw [Finset.card_sdiff_of_subset htransversalResidual, hresidualCard]
    omega
  obtain ⟨sample, hsampleRest, hsampleCard⟩ :=
    Finset.exists_subset_card_eq hrestCard
  have hsampleSupport : sample ⊆ support :=
    hsampleRest.trans (Finset.sdiff_subset.trans Finset.sdiff_subset)
  obtain ⟨secondary, hsecondarySample, hsecondaryCard, hsecondaryCap⟩ :=
    hdense sample hsampleSupport hsampleCard
  have hsecondaryRest : secondary ⊆ rest :=
    hsecondarySample.trans hsampleRest
  have hsecondaryResidual : secondary ⊆ residual :=
    hsecondaryRest.trans Finset.sdiff_subset
  have hsecondarySupport : secondary ⊆ support :=
    hsecondaryRest.trans (Finset.sdiff_subset.trans Finset.sdiff_subset)
  have hfixedSecondary : Disjoint fixed secondary := by
    rw [Finset.disjoint_left]
    intro x hxFixed hxSecondary
    exact (Finset.mem_sdiff.mp (hsecondaryResidual hxSecondary)).2 hxFixed
  have htransversalSecondary : Disjoint transversal secondary := by
    rw [Finset.disjoint_left]
    intro x hxTransversal hxSecondary
    exact (Finset.mem_sdiff.mp (hsecondaryRest hxSecondary)).2 hxTransversal
  exact (hhits secondary
    (mem_capWitnesses.mpr
      ⟨hsecondarySupport, hsecondaryCard, hsecondaryCap⟩)
    hfixedSecondary) htransversalSecondary

/-- Every finite residual-cap transversal contains a minimum-cardinality
subtransversal.  Each selected vertex is essential: deleting it exposes a
four-cap disjoint from both the fixed cap and all other selected vertices. -/
theorem exists_minimal_residualCapTransversal_with_private_caps
    {n : ℕ} {χ : TripleColoring n}
    {support fixed tails : Finset (Fin n)}
    (htails : HitsEveryFourCapDisjointFrom χ support fixed tails) :
    ∃ transversal,
      transversal ⊆ tails ∧
      HitsEveryFourCapDisjointFrom χ support fixed transversal ∧
      ∀ x ∈ transversal, ∃ secondary,
        secondary ∈ capWitnesses χ support 4 ∧
        Disjoint fixed secondary ∧ x ∈ secondary ∧
        Disjoint (transversal.erase x) secondary := by
  classical
  let P : ℕ → Prop := fun k ↦ ∃ transversal,
    transversal ⊆ tails ∧
    HitsEveryFourCapDisjointFrom χ support fixed transversal ∧
    transversal.card = k
  have hP : ∃ k, P k := ⟨tails.card, tails, Finset.Subset.rfl, htails, rfl⟩
  obtain ⟨transversal, htransversalSub, htransversalHits, hcard⟩ :=
    Nat.find_spec hP
  refine ⟨transversal, htransversalSub, htransversalHits, ?_⟩
  intro x hx
  have hnotHits :
      ¬HitsEveryFourCapDisjointFrom χ support fixed
        (transversal.erase x) := by
    intro heraseHits
    have heraseSub : transversal.erase x ⊆ tails :=
      Finset.erase_subset x transversal |>.trans htransversalSub
    have hminimal := Nat.find_min' hP
      ⟨transversal.erase x, heraseSub, heraseHits, rfl⟩
    rw [← hcard, Finset.card_erase_of_mem hx] at hminimal
    have hpositive : 0 < transversal.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  unfold HitsEveryFourCapDisjointFrom at hnotHits
  push Not at hnotHits
  obtain ⟨secondary, hsecondary, hfixedSecondary, heraseSecondary⟩ :=
    hnotHits
  have hmeets := htransversalHits secondary hsecondary hfixedSecondary
  obtain ⟨y, hyTransversal, hySecondary⟩ := Finset.not_disjoint_iff.mp hmeets
  have hyx : y = x := by
    by_contra hyx
    exact (Finset.disjoint_left.mp heraseSecondary)
      (Finset.mem_erase.mpr ⟨hyx, hyTransversal⟩) hySecondary
  subst y
  exact ⟨secondary, hsecondary, hfixedSecondary, hySecondary,
    heraseSecondary⟩

/-- A private witness cap meets its minimum transversal in exactly the vertex
that owns it. -/
theorem privateCap_inter_transversal_eq_singleton
    {α : Type*} [DecidableEq α] {transversal secondary : Finset α} {x : α}
    (hxTransversal : x ∈ transversal) (hxSecondary : x ∈ secondary)
    (hprivate : Disjoint (transversal.erase x) secondary) :
    transversal ∩ secondary = {x} := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hyTransversal, hySecondary⟩
    by_contra hyx
    exact (Finset.disjoint_left.mp hprivate)
      (Finset.mem_erase.mpr ⟨hyx, hyTransversal⟩) hySecondary
  · rintro rfl
    exact ⟨hxTransversal, hxSecondary⟩

/-- Every four-cap disjoint from a terminal four-cap meets the terminal cap's
genuine outer-tail set. -/
theorem terminalCap_disjoint_fourCap_meets_outerTail
    {n : ℕ} {χ : TripleColoring n} {support terminal secondary : Finset (Fin n)}
    (hterminalCap : terminal ∈ capWitnesses χ support 4)
    (hterminal : ¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)))
    (hsecondary : secondary ∈ capWitnesses χ support 4)
    (hdisjoint : Disjoint secondary terminal) :
    ¬Disjoint secondary
      ((support \ openSweepSpanVertices support terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal) := by
  intro hmiss
  let hterminalNonempty := capWitness_nonempty_of_mem (by omega) hterminalCap
  have hsecondaryOpen :
      secondary ⊆ openSweepSpanVertices support terminal hterminalNonempty := by
    intro x hxSecondary
    have hxSupport := (mem_capWitnesses.mp hsecondary).1 hxSecondary
    by_contra hxOpen
    have hxNotTerminal : x ∉ terminal :=
      (Finset.disjoint_left.mp hdisjoint) hxSecondary
    have hxTail : x ∈
        (support \ openSweepSpanVertices support terminal hterminalNonempty) \
          terminal :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxSupport, hxOpen⟩,
        hxNotTerminal⟩
    exact (Finset.disjoint_left.mp hmiss) hxSecondary hxTail
  apply hterminal
  refine ⟨secondary, hsecondary, ?_⟩
  exact finsetSweepInterval_strictlyInside_of_subset_openSweepSpan
    hterminalNonempty (capWitness_nonempty_of_mem (by omega) hsecondary)
    hsecondaryOpen

/-- In a `32/23` dense support, the terminal-tail set contains a
minimum-cardinality residual-cap transversal of size at least six.  Every
selected tail owns a private secondary cap after the other selected tails are
deleted. -/
theorem exists_six_private_terminalTail_transversal_at_32_23
    {n : ℕ} {χ : TripleColoring n}
    {support terminal : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hterminalCap : terminal ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap))) :
    let tails := (support \ openSweepSpanVertices support terminal
      (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal
    ∃ transversal,
      transversal ⊆ tails ∧ 6 ≤ transversal.card ∧
      HitsEveryFourCapDisjointFrom χ support terminal transversal ∧
      ∀ x ∈ transversal, ∃ secondary,
        secondary ∈ capWitnesses χ support 4 ∧
        Disjoint terminal secondary ∧ x ∈ secondary ∧
        Disjoint (transversal.erase x) secondary := by
  dsimp only
  let tails := (support \ openSweepSpanVertices support terminal
    (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal
  have htailsSub : tails ⊆ support :=
    Finset.sdiff_subset.trans Finset.sdiff_subset
  have hterminalTails : Disjoint terminal tails := by
    rw [Finset.disjoint_left]
    intro x hxTerminal hxTails
    exact (Finset.mem_sdiff.mp hxTails).2 hxTerminal
  have htailsHits :
      HitsEveryFourCapDisjointFrom χ support terminal tails := by
    intro secondary hsecondary hterminalSecondary hmiss
    exact (terminalCap_disjoint_fourCap_meets_outerTail
      hterminalCap hterminal hsecondary hterminalSecondary.symm) hmiss.symm
  obtain ⟨transversal, htransversalTails, htransversalHits, hprivate⟩ :=
    exists_minimal_residualCapTransversal_with_private_caps htailsHits
  have htransversalSub : transversal ⊆ support :=
    htransversalTails.trans htailsSub
  have hterminalTransversal : Disjoint terminal transversal :=
    hterminalTails.mono_right htransversalTails
  have htransversalCard := six_le_residualCapTransversal_at_32_23
    hsupportCard hterminalCap htransversalSub hterminalTransversal hdense
    htransversalHits
  exact ⟨transversal, htransversalTails, htransversalCard,
    htransversalHits, hprivate⟩

/-- A fixed terminal cap in a `32/23` dense reservoir has two disjoint
secondary caps carrying two distinct genuine outer-tail vertices. -/
theorem exists_two_disjoint_secondaryCaps_with_distinct_outerTails_at_32_23
    {n : ℕ} {χ : TripleColoring n} {support terminal : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hterminalCap : terminal ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap))) :
    let tails := (support \ openSweepSpanVertices support terminal
      (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal
    ∃ first second x y,
      first ∈ capWitnesses χ support 4 ∧
      second ∈ capWitnesses χ support 4 ∧
      Disjoint terminal first ∧ Disjoint terminal second ∧
      Disjoint first second ∧
      x ∈ first ∧ x ∈ tails ∧ y ∈ second ∧ y ∈ tails ∧ x ≠ y := by
  dsimp only
  obtain ⟨first, second, hfirst, hsecond, hterminalFirst,
      hterminalSecond, hfirstSecond⟩ :=
    exists_two_fourCaps_pairwiseDisjoint_from_given_at_32_23
      hsupportCard hterminalCap hdense
  have hfirstMeets := terminalCap_disjoint_fourCap_meets_outerTail
    hterminalCap hterminal hfirst hterminalFirst.symm
  have hsecondMeets := terminalCap_disjoint_fourCap_meets_outerTail
    hterminalCap hterminal hsecond hterminalSecond.symm
  obtain ⟨x, hxFirst, hxTail⟩ := Finset.not_disjoint_iff.mp hfirstMeets
  obtain ⟨y, hySecond, hyTail⟩ := Finset.not_disjoint_iff.mp hsecondMeets
  have hxy : x ≠ y := by
    intro hxy
    subst y
    exact (Finset.disjoint_left.mp hfirstSecond) hxFirst hySecond
  exact ⟨first, second, x, y, hfirst, hsecond, hterminalFirst,
    hterminalSecond, hfirstSecond, hxFirst, hxTail, hySecond, hyTail, hxy⟩

/-- The two secondary caps can be marked by distinct terminal tails, each of
which is routed into the lowest node or into a lower first-exit bucket. -/
theorem exists_two_disjoint_secondaryCaps_with_routed_outerTails_at_32_23
    {n : ℕ} {χ : TripleColoring n} {support terminal : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hterminalCap : terminal ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)))
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : DecompositionTree.IsLowestSeparatingPath terminal tree path)
    (hbridge : ∀ x ∈
      (support \ openSweepSpanVertices support terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal,
      RealizesCapFourFailureSignature χ terminal
          (mem_capWitnesses.mp hterminalCap).2.1 x .before ∨
        RealizesCapFourFailureSignature χ terminal
          (mem_capWitnesses.mp hterminalCap).2.1 x .after) :
    let tails := (support \ openSweepSpanVertices support terminal
      (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal
    ∃ first second x y,
      first ∈ capWitnesses χ support 4 ∧
      second ∈ capWitnesses χ support 4 ∧
      Disjoint terminal first ∧ Disjoint terminal second ∧
      Disjoint first second ∧
      x ∈ first ∧ x ∈ tails ∧ y ∈ second ∧ y ∈ tails ∧ x ≠ y ∧
      IsInternalOrLowerFirstExit terminal x tree path node ∧
      IsInternalOrLowerFirstExit terminal y tree path node := by
  dsimp only
  obtain ⟨first, second, x, y, hfirst, hsecond, hterminalFirst,
      hterminalSecond, hfirstSecond, hxFirst, hxTail, hySecond, hyTail, hxy⟩ :=
    exists_two_disjoint_secondaryCaps_with_distinct_outerTails_at_32_23
      hsupportCard hterminalCap hdense hterminal
  have htailSupport :
      (support \ openSweepSpanVertices support terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal ⊆
        support := by
    exact Finset.sdiff_subset.trans Finset.sdiff_subset
  have hxRoute := internal_or_lowerFirstExit_of_endpointBridge
    hlookup hallocated (mem_capWitnesses.mp hterminalCap).2.1
    (htailSupport hxTail) (hbridge x hxTail)
  have hyRoute := internal_or_lowerFirstExit_of_endpointBridge
    hlookup hallocated (mem_capWitnesses.mp hterminalCap).2.1
    (htailSupport hyTail) (hbridge y hyTail)
  exact ⟨first, second, x, y, hfirst, hsecond, hterminalFirst,
    hterminalSecond, hfirstSecond, hxFirst, hxTail, hySecond, hyTail, hxy,
    hxRoute, hyRoute⟩

/-- Package the terminal-relative secondary-cap theorem in its reusable routed
pair predicate. -/
theorem hasTwoRoutedSecondaryCaps_of_terminal_at_32_23
    {n : ℕ} {χ : TripleColoring n} {support terminal : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hterminalCap : terminal ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)))
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : DecompositionTree.IsLowestSeparatingPath terminal tree path)
    (hbridge : ∀ x ∈
      (support \ openSweepSpanVertices support terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal,
      RealizesCapFourFailureSignature χ terminal
          (mem_capWitnesses.mp hterminalCap).2.1 x .before ∨
        RealizesCapFourFailureSignature χ terminal
          (mem_capWitnesses.mp hterminalCap).2.1 x .after) :
    HasTwoRoutedSecondaryCaps χ support terminal
      ((support \ openSweepSpanVertices support terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal)
      tree path node := by
  simpa [HasTwoRoutedSecondaryCaps] using
    exists_two_disjoint_secondaryCaps_with_routed_outerTails_at_32_23
      hsupportCard hterminalCap hdense hterminal tree hlookup hallocated hbridge

/-- Package the minimum terminal-tail transversal and route all of its
essential vertices at the lowest cap node. -/
theorem hasSixPrivateRoutedTailTransversal_of_terminal_at_32_23
    {n : ℕ} {χ : TripleColoring n} {support terminal : Finset (Fin n)}
    (hsupportCard : support.card = 32)
    (hterminalCap : terminal ∈ capWitnesses χ support 4)
    (hdense : ∀ subset : Finset (Fin n), subset ⊆ support →
      subset.card = 23 → ContainsCapSet χ subset 4)
    (hterminal : ¬∃ inner, ∃ hinner : inner ∈ capWitnesses χ support 4,
      (finsetSweepInterval inner
        (capWitness_nonempty_of_mem (by omega) hinner)).StrictlyInside
      (finsetSweepInterval terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)))
    (tree : DecompositionTree χ support) {path : List Bool}
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (hallocated : DecompositionTree.IsLowestSeparatingPath terminal tree path)
    (hbridge : ∀ x ∈
      (support \ openSweepSpanVertices support terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal,
      RealizesCapFourFailureSignature χ terminal
          (mem_capWitnesses.mp hterminalCap).2.1 x .before ∨
        RealizesCapFourFailureSignature χ terminal
          (mem_capWitnesses.mp hterminalCap).2.1 x .after) :
    HasSixPrivateRoutedTailTransversal χ support terminal
      ((support \ openSweepSpanVertices support terminal
        (capWitness_nonempty_of_mem (by omega) hterminalCap)) \ terminal)
      tree path node := by
  obtain ⟨transversal, htransversalTails, hcard, hhits, hprivate⟩ :=
    exists_six_private_terminalTail_transversal_at_32_23
      hsupportCard hterminalCap hdense hterminal
  refine ⟨transversal, htransversalTails, hcard, hhits, hprivate, ?_⟩
  intro x hxTransversal
  have hxTail := htransversalTails hxTransversal
  have hxSupport : x ∈ support :=
    Finset.sdiff_subset.trans Finset.sdiff_subset hxTail
  exact internal_or_lowerFirstExit_of_endpointBridge
    hlookup hallocated (mem_capWitnesses.mp hterminalCap).2.1
    hxSupport (hbridge x hxTail)

/-- Six vertices partitioned by a finite region leave at least three on one
side of the partition. -/
theorem three_le_inter_or_sdiff_of_six_le_card
    {α : Type*} [DecidableEq α] (s region : Finset α)
    (hcard : 6 ≤ s.card) :
    3 ≤ (s ∩ region).card ∨ 3 ≤ (s \ region).card := by
  have hpartition := Finset.card_sdiff_add_card_inter s region
  omega

/-- The six essential routed tails yield either three private internal tails,
or three private external tails; every external selected tail has a certified
lower-directed first exit. -/
theorem HasSixPrivateRoutedTailTransversal.three_internal_or_external
    {n : ℕ} {χ : TripleColoring n} {support terminal tails : Finset (Fin n)}
    {tree : DecompositionTree χ support} {path : List Bool}
    {node : DecompositionSplit χ}
    (h : HasSixPrivateRoutedTailTransversal χ support terminal tails
      tree path node) :
    ∃ transversal,
      transversal ⊆ tails ∧
      HitsEveryFourCapDisjointFrom χ support terminal transversal ∧
      (∀ x ∈ transversal, ∃ secondary,
        secondary ∈ capWitnesses χ support 4 ∧
        Disjoint terminal secondary ∧ x ∈ secondary ∧
        Disjoint (transversal.erase x) secondary) ∧
      (3 ≤ (transversal ∩ (node.lower ∪ node.upper)).card ∨
        (3 ≤ (transversal \ (node.lower ∪ node.upper)).card ∧
          ∀ x ∈ transversal \ (node.lower ∪ node.upper),
            DecompositionTree.FirstExitAlongPath terminal x tree path false)) := by
  obtain ⟨transversal, htransversalTails, hcard, hhits, hprivate, hroutes⟩ := h
  refine ⟨transversal, htransversalTails, hhits, hprivate, ?_⟩
  rcases three_le_inter_or_sdiff_of_six_le_card transversal
      (node.lower ∪ node.upper) hcard with hinternal | hexternal
  · exact Or.inl hinternal
  · refine Or.inr ⟨hexternal, ?_⟩
    intro x hxExternal
    have hxData := Finset.mem_sdiff.mp hxExternal
    rcases hroutes x hxData.1 with hxInternal | hxExit
    · exact False.elim (hxData.2 hxInternal)
    · exact hxExit

/-- The actual singleton-lower `(5,7,8)` obstruction has one terminal cap
carrying both its lowest-split alternative and a pair of globally supplied
secondary caps routed through distinct terminal tails. -/
theorem exists_terminalFourCap_twoRoutedSecondaryCaps_at_578
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
        HasTwoRoutedSecondaryCaps χ upper cap tails tree path node := by
  obtain ⟨cap, hcap, hterminal, hstraddles, htail, hbridge,
      tree, path, node, hlookup, hallocated, halternative⟩ :=
    exists_terminalFourCap_nineTail_lowestSplit_at_578
      hupper hroot hupperCard hstate558 hnoCap hnoCup hnoStrong
  have hdense :=
    (dense_straddling_cap_reservoir_at_578
      hupper hroot hnoCap hnoCup hnoStrong).1
  have hrouted := hasTwoRoutedSecondaryCaps_of_terminal_at_32_23
    hupperCard hcap hdense hterminal tree hlookup hallocated hbridge
  exact ⟨cap, hcap, hterminal, hstraddles, htail, tree, path, node,
    hlookup, hallocated, halternative, hrouted⟩

/-- The actual singleton-lower `(5,7,8)` obstruction carries at least six
essential terminal tails.  Each has a private secondary cap and is routed at
the terminal cap's lowest decomposition node. -/
theorem exists_terminalFourCap_sixPrivateRoutedTailTransversal_at_578
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
        HasSixPrivateRoutedTailTransversal χ upper cap tails tree path node := by
  obtain ⟨cap, hcap, hterminal, hstraddles, htail, hbridge,
      tree, path, node, hlookup, hallocated, halternative⟩ :=
    exists_terminalFourCap_nineTail_lowestSplit_at_578
      hupper hroot hupperCard hstate558 hnoCap hnoCup hnoStrong
  have hdense :=
    (dense_straddling_cap_reservoir_at_578
      hupper hroot hnoCap hnoCup hnoStrong).1
  have hrouted :=
    hasSixPrivateRoutedTailTransversal_of_terminal_at_32_23
      hupperCard hcap hdense hterminal tree hlookup hallocated hbridge
  exact ⟨cap, hcap, hterminal, hstraddles, htail, tree, path, node,
    hlookup, hallocated, halternative, hrouted⟩

end ErdosSzekeres

end
