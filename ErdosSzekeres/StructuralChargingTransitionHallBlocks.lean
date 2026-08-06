module

public import ErdosSzekeres.StructuralChargingTransitionHallRayBridge

@[expose] public section

/-!
# Consecutive blocks of the exact-rank frontier

The retained exact-rank frontier is linearly ordered by either endpoint.  This
file defines its intrinsic consecutive blocks using left endpoints, proves
that every nonempty consecutive subfamily is exactly one such block, and
freezes consecutive-block expansion as a separate target from full Hall.

It also records a deliberately strong sufficient condition: injectivity of
the active-ray representative on every block.  The condition is exposed for
bounded falsification; it is not assumed to follow from the existing ray
bridge.
-/

namespace ErdosSzekeres

noncomputable section

/-- The subtype of retained exact-rank spans at one allocated split. -/
abbrev AllocatedExactRankFrontierSpan {n : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn) (rank : ℕ) :=
  {span // span ∈ allocatedExactRankFrontier chi lower upper color rank}

/-- The closed block of retained spans between two frontier endpoints. -/
def allocatedExactRankFrontierBlock
    {n rank : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (first last : AllocatedExactRankFrontierSpan
      chi lower upper color rank) :
    Finset (AllocatedExactRankFrontierSpan chi lower upper color rank) :=
  Finset.univ.filter fun span ↦
    first.1.left ≤ span.1.left ∧ span.1.left ≤ last.1.left

@[simp] theorem mem_allocatedExactRankFrontierBlock
    {n rank : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    {first last span : AllocatedExactRankFrontierSpan
      chi lower upper color rank} :
    span ∈ allocatedExactRankFrontierBlock first last ↔
      first.1.left ≤ span.1.left ∧ span.1.left ≤ last.1.left := by
  simp [allocatedExactRankFrontierBlock]

/-- The frontier's left- and right-endpoint orders also agree non-strictly. -/
theorem allocatedExactRankFrontier_left_le_iff_right_le
    {n rank : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    {first second : AllocatedExactRankFrontierSpan
      chi lower upper color rank} :
    first.1.left ≤ second.1.left ↔ first.1.right ≤ second.1.right := by
  simp only [← not_lt]
  exact not_congr (allocatedExactRankFrontier_left_lt_iff_right_lt
    second.2 first.2)

/-- The same frontier block is obtained by filtering on right endpoints. -/
theorem mem_allocatedExactRankFrontierBlock_iff_right
    {n rank : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    {first last span : AllocatedExactRankFrontierSpan
      chi lower upper color rank} :
    span ∈ allocatedExactRankFrontierBlock first last ↔
      first.1.right ≤ span.1.right ∧ span.1.right ≤ last.1.right := by
  rw [mem_allocatedExactRankFrontierBlock,
    allocatedExactRankFrontier_left_le_iff_right_le,
    allocatedExactRankFrontier_left_le_iff_right_le]

/-- A subfamily is consecutive when it contains every retained frontier span
between any two of its members. -/
def AllocatedExactRankFrontierLeftConsecutive
    {n rank : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (spans : Finset (AllocatedExactRankFrontierSpan
      chi lower upper color rank)) : Prop :=
  ∀ first ∈ spans, ∀ last ∈ spans,
    first.1.left ≤ last.1.left →
      allocatedExactRankFrontierBlock first last ⊆ spans

/-- Every endpoint-defined frontier block is consecutive. -/
theorem allocatedExactRankFrontierBlock_leftConsecutive
    {n rank : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (first last : AllocatedExactRankFrontierSpan
      chi lower upper color rank) :
    AllocatedExactRankFrontierLeftConsecutive
      (allocatedExactRankFrontierBlock first last) := by
  intro a ha b hb _ x hx
  rw [mem_allocatedExactRankFrontierBlock] at ha hb hx ⊢
  exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩

/-- Every nonempty consecutive subfamily is the block between one of its
minimal and one of its maximal left endpoints. -/
theorem AllocatedExactRankFrontierLeftConsecutive.eq_block_of_nonempty
    {n rank : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    {spans : Finset (AllocatedExactRankFrontierSpan
      chi lower upper color rank)}
    (hconsecutive : AllocatedExactRankFrontierLeftConsecutive spans)
    (hne : spans.Nonempty) :
    ∃ first last, first ∈ spans ∧ last ∈ spans ∧
      first.1.left ≤ last.1.left ∧
        spans = allocatedExactRankFrontierBlock first last := by
  obtain ⟨first, hfirst, hmin⟩ :=
    spans.exists_min_image (fun span ↦ span.1.left) hne
  obtain ⟨last, hlast, hmax⟩ :=
    spans.exists_max_image (fun span ↦ span.1.left) hne
  refine ⟨first, last, hfirst, hlast, hmin last hlast, ?_⟩
  apply Finset.Subset.antisymm
  · intro span hspan
    rw [mem_allocatedExactRankFrontierBlock]
    exact ⟨hmin span hspan, hmax span hspan⟩
  · exact hconsecutive first hfirst last hlast (hmin last hlast)

/-- Hall expansion restricted to endpoint-defined consecutive blocks. -/
def AllocatedReflectedEndpointRankTransitionBlockExpansion
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ first last : AllocatedExactRankFrontierSpan
      chi lower upper color rank,
    let spans := allocatedExactRankFrontierBlock first last
    spans.card ≤
      (spans.biUnion (allocatedReflectedEndpointRankTransitionCandidates
        chi lower upper color hrank hrankTop)).card

/-- Consecutive-block expansion using only the endpoint interval incident to
the actual child ray.  This is stronger than expansion by the union of both
endpoint intervals but weaker than injectivity of one chosen representative. -/
def AllocatedReflectedActiveEndpointRankTransitionBlockExpansion
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ first last : AllocatedExactRankFrontierSpan
      chi lower upper color rank,
    let spans := allocatedExactRankFrontierBlock first last
    spans.card ≤
      (spans.biUnion
        (allocatedReflectedActiveEndpointRankTransitionCandidates
          chi lower upper color hrank hrankTop)).card

/-- Expansion by the active endpoint intervals implies the original
two-endpoint consecutive-block target. -/
theorem allocatedReflectedEndpointRankTransitionBlockExpansion_of_active
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hactive : AllocatedReflectedActiveEndpointRankTransitionBlockExpansion
      chi lower upper color hrank hrankTop) :
    AllocatedReflectedEndpointRankTransitionBlockExpansion
      chi lower upper color hrank hrankTop := by
  intro first last
  let spans := allocatedExactRankFrontierBlock first last
  calc
    spans.card ≤
        (spans.biUnion
          (allocatedReflectedActiveEndpointRankTransitionCandidates
            chi lower upper color hrank hrankTop)).card :=
      hactive first last
    _ ≤
        (spans.biUnion (allocatedReflectedEndpointRankTransitionCandidates
          chi lower upper color hrank hrankTop)).card :=
      Finset.card_le_card (Finset.biUnion_mono (fun span _ ↦
        allocatedReflectedActiveEndpointRankTransitionCandidates_subset
          chi lower upper color hrank hrankTop span))

/-- The same restricted Hall condition quantified over intrinsically
consecutive subfamilies. -/
def AllocatedReflectedEndpointRankTransitionConsecutiveHall
    {n rank k : ℕ} (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (color : Turn)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ spans : Finset (AllocatedExactRankFrontierSpan
      chi lower upper color rank),
    AllocatedExactRankFrontierLeftConsecutive spans →
      spans.card ≤
        (spans.biUnion (allocatedReflectedEndpointRankTransitionCandidates
          chi lower upper color hrank hrankTop)).card

/-- Endpoint blocks and nonempty intrinsic consecutive subfamilies describe
the same restricted Hall target. -/
theorem allocatedReflectedEndpointRankTransitionBlockExpansion_iff_consecutiveHall
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    {hrank : 1 ≤ rank} {hrankTop : rank < k} :
    AllocatedReflectedEndpointRankTransitionBlockExpansion
        chi lower upper color hrank hrankTop ↔
      AllocatedReflectedEndpointRankTransitionConsecutiveHall
        chi lower upper color hrank hrankTop := by
  constructor
  · intro hblocks spans hconsecutive
    by_cases hne : spans.Nonempty
    · obtain ⟨first, last, _, _, _, hspans⟩ :=
        hconsecutive.eq_block_of_nonempty hne
      rw [hspans]
      exact hblocks first last
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  · intro hconsecutive first last
    exact hconsecutive (allocatedExactRankFrontierBlock first last)
      (allocatedExactRankFrontierBlock_leftConsecutive first last)

/-- A selected candidate that is injective on a finite family witnesses its
Hall inequality. -/
theorem Finset.card_le_biUnion_card_of_injective_mem
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (spans : Finset α) (candidates : α → Finset β)
    (representative : α → β)
    (hmem : ∀ span ∈ spans, representative span ∈ candidates span)
    (hinjective : Set.InjOn representative spans) :
    spans.card ≤ (spans.biUnion candidates).card := by
  calc
    spans.card = (spans.image representative).card :=
      (Finset.card_image_iff.mpr hinjective).symm
    _ ≤ (spans.biUnion candidates).card := Finset.card_le_card (by
      rw [Finset.image_subset_iff]
      intro span hspan
      rw [Finset.mem_biUnion]
      exact ⟨span, hspan, hmem span hspan⟩)

/-- Injectivity of the active-ray representative on each block is sufficient
for consecutive-block expansion.  This deliberately strong premise is a
falsification target, not a proved geometric property. -/
theorem allocatedReflectedEndpointRankTransitionBlockExpansion_of_active_injOn
    {n rank k : ℕ} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {color : Turn}
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hinjective : ∀ first last : AllocatedExactRankFrontierSpan
        chi lower upper color rank,
      Set.InjOn
        (allocatedReflectedActiveEndpointRankTransitionCandidate
          chi lower upper color hrank hrankTop)
        (allocatedExactRankFrontierBlock first last)) :
    AllocatedReflectedEndpointRankTransitionBlockExpansion
      chi lower upper color hrank hrankTop := by
  intro first last
  apply Finset.card_le_biUnion_card_of_injective_mem
    (representative := allocatedReflectedActiveEndpointRankTransitionCandidate
      chi lower upper color hrank hrankTop)
  · intro span _
    exact allocatedReflectedActiveEndpointRankTransitionCandidate_mem
      chi lower upper color hrank hrankTop span
  · exact hinjective first last

end

end ErdosSzekeres

end
