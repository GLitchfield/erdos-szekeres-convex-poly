module

public import ErdosSzekeres.StructuralChargingResidualReplacement567

@[expose] public section

/-!
# Four light repairs from a state-567 same-occupancy collision

This file amplifies two distinct light probe witnesses into four pairwise
distinct light witnesses.  It records the resulting avoidance network without
asserting that the network is contradictory.
-/

namespace ErdosSzekeres

/-- Four light incident witnesses with a triangular residual-avoidance
network.  The first two witnesses and their probe blocks are parameters, so
the structure retains their exact incidences without requiring the two blocks
to be distinct. -/
structure LightSameOccupancyFourRepairNetwork567 {n : ℕ}
    (χ : TripleColoring n) (ambient first second : Finset (Fin n))
    (a b : Fin n) (block₁ block₂ third₁ third₂ : Finset (Fin n)) where
  initial₁ : IsCarrierTouchingProbeWitness567 χ ambient first second
    a b block₁ third₁
  initial₂ : IsCarrierTouchingProbeWitness567 χ ambient first second
    a b block₂ third₂
  initial_ne : third₁ ≠ third₂
  same_occupancy : SameCarrierTouchingOccupancy567 first second third₁ third₂
  light₁ : (third₁ ∩ (first ∪ second)).card ≤ 2
  light₂ : (third₂ ∩ (first ∪ second)).card ≤ 2
  block₃ : Finset (Fin n)
  block₄ : Finset (Fin n)
  third₃ : Finset (Fin n)
  third₄ : Finset (Fin n)
  incident₃ : IsCarrierTouchingProbeWitness567 χ ambient first second
    a b block₃ third₃
  incident₄ : IsCarrierTouchingProbeWitness567 χ ambient first second
    a b block₄ third₄
  light₃ : (third₃ ∩ (first ∪ second)).card ≤ 2
  light₄ : (third₄ ∩ (first ∪ second)).card ≤ 2
  x₁ : Fin n
  x₂ : Fin n
  x₃ : Fin n
  x₁_residual : x₁ ∈ ambient \ (first ∪ second)
  x₂_residual : x₂ ∈ ambient \ (first ∪ second)
  x₃_residual : x₃ ∈ ambient \ (first ∪ second)
  x₁_mem_third₁ : x₁ ∈ third₁
  x₂_mem_third₂ : x₂ ∈ third₂
  x₃_mem_third₃ : x₃ ∈ third₃
  x₁_ne_x₂ : x₁ ≠ x₂
  x₁_ne_x₃ : x₁ ≠ x₃
  x₂_ne_x₃ : x₂ ≠ x₃
  x₁_mem_block₃ : x₁ ∈ block₃
  x₂_mem_block₃ : x₂ ∈ block₃
  x₁_mem_block₄ : x₁ ∈ block₄
  x₂_mem_block₄ : x₂ ∈ block₄
  x₃_mem_block₄ : x₃ ∈ block₄
  x₁_not_mem_third₃ : x₁ ∉ third₃
  x₂_not_mem_third₃ : x₂ ∉ third₃
  x₁_not_mem_third₄ : x₁ ∉ third₄
  x₂_not_mem_third₄ : x₂ ∉ third₄
  x₃_not_mem_third₄ : x₃ ∉ third₄
  third₁_ne_third₃ : third₁ ≠ third₃
  third₁_ne_third₄ : third₁ ≠ third₄
  third₂_ne_third₃ : third₂ ≠ third₃
  third₂_ne_third₄ : third₂ ≠ third₄
  third₃_ne_third₄ : third₃ ≠ third₄

/-- A same-occupancy collision either already exposes an incident witness
with at least three carrier vertices, or it amplifies to four pairwise
distinct light incident witnesses with triangular residual avoidance. -/
theorem lightSameOccupancyCollision567_has_four_repair_network
    {n : ℕ} {χ : TripleColoring n}
    {ambient first second : Finset (Fin n)}
    (hescape : PackedInternalPairFourResidualEscape χ ambient first second)
    (hnoStrongSeven : ¬ContainsStrongPolygonSet χ ambient 7)
    {a b : Fin n} (ha : a ∈ first) (hb : b ∈ second)
    {block₁ block₂ third₁ third₂ : Finset (Fin n)}
    (hincident₁ : IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block₁ third₁)
    (hincident₂ : IsCarrierTouchingProbeWitness567 χ ambient first second
      a b block₂ third₂)
    (hthirdNe : third₁ ≠ third₂)
    (hsame : SameCarrierTouchingOccupancy567 first second third₁ third₂) :
    (∃ block third,
      IsCarrierTouchingProbeWitness567 χ ambient first second
        a b block third ∧
      3 ≤ (third ∩ (first ∪ second)).card) ∨
    Nonempty (LightSameOccupancyFourRepairNetwork567 χ ambient first second a b
      block₁ block₂ third₁ third₂) := by
  classical
  let residual := ambient \ (first ∪ second)
  have hresidualCard : residual.card = 10 := by
    simpa [residual] using hescape.1
  have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 7 := by
    intro hstrong
    exact hnoStrongSeven
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
  by_cases hheavy : ∃ block third,
      IsCarrierTouchingProbeWitness567 χ ambient first second
        a b block third ∧
      3 ≤ (third ∩ (first ∪ second)).card
  · exact Or.inl hheavy
  · right
    have light_of_incident {block third : Finset (Fin n)}
        (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
          a b block third) :
        (third ∩ (first ∪ second)).card ≤ 2 := by
      by_contra hlight
      apply hheavy
      exact ⟨block, third, hincident, by omega⟩
    have trace_card_ge_four {block third : Finset (Fin n)}
        (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
          a b block third)
        (hlight : (third ∩ (first ∪ second)).card ≤ 2) :
        4 ≤ (third ∩ residual).card := by
      have hsplit := hincident.carrier_add_residual_card
      change (third ∩ (first ∪ second)).card +
        (third ∩ residual).card = 6 at hsplit
      omega
    have avoids_block {block third : Finset (Fin n)} {x : Fin n}
        (hincident : IsCarrierTouchingProbeWitness567 χ ambient first second
          a b block third) (hxBlock : x ∈ block) : x ∉ third := by
      intro hxThird
      have hxAvoid := Finset.mem_sdiff.mp (hincident.2.1 hxThird)
      exact hxAvoid.2 (by simp [hxBlock])
    have hlight₁ := light_of_incident hincident₁
    have hlight₂ := light_of_incident hincident₂
    have htrace₁Card := trace_card_ge_four hincident₁ hlight₁
    have htrace₂Card := trace_card_ge_four hincident₂ hlight₂
    obtain ⟨x₁, hx₁Trace⟩ : (third₁ ∩ residual).Nonempty :=
      Finset.card_pos.mp (by omega)
    have htrace₂Nontrivial : (third₂ ∩ residual).Nontrivial :=
      Finset.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨x₂, hx₂Erase⟩ := htrace₂Nontrivial.erase_nonempty (a := x₁)
    have hx₂Trace : x₂ ∈ third₂ ∩ residual :=
      (Finset.mem_erase.mp hx₂Erase).2
    have hx₂NeX₁ : x₂ ≠ x₁ := (Finset.mem_erase.mp hx₂Erase).1
    have hx₁NeX₂ : x₁ ≠ x₂ := hx₂NeX₁.symm
    have hx₁Third₁ : x₁ ∈ third₁ := (Finset.mem_inter.mp hx₁Trace).1
    have hx₁Residual : x₁ ∈ residual := (Finset.mem_inter.mp hx₁Trace).2
    have hx₂Third₂ : x₂ ∈ third₂ := (Finset.mem_inter.mp hx₂Trace).1
    have hx₂Residual : x₂ ∈ residual := (Finset.mem_inter.mp hx₂Trace).2
    let pair₁₂ : Finset (Fin n) := {x₁, x₂}
    have hpair₁₂Sub : pair₁₂ ⊆ residual := by
      intro x hx
      simp only [pair₁₂, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hx₁Residual
      · exact hx₂Residual
    have hpair₁₂Card : pair₁₂.card = 2 := by
      simp [pair₁₂, hx₁NeX₂]
    obtain ⟨triple₁₂, hpairTriple, htriple₁₂Sub, htriple₁₂Card⟩ :=
      Finset.exists_subsuperset_card_eq hpair₁₂Sub (by omega)
        (show 3 ≤ residual.card by omega)
    obtain ⟨block₃, hblock₃Bad, htripleBlock₃⟩ :=
      badResidualFourBlocks567_covers_three hresidualCard hnoStrongResidual
        htriple₁₂Sub htriple₁₂Card
    obtain ⟨third₃, hincident₃⟩ :=
      hescape.badProbe_has_incident_witness ha hb
        (by simpa [residual] using hblock₃Bad)
    have hlight₃ := light_of_incident hincident₃
    have hx₁Pair : x₁ ∈ pair₁₂ := by simp [pair₁₂]
    have hx₂Pair : x₂ ∈ pair₁₂ := by simp [pair₁₂]
    have hx₁Block₃ : x₁ ∈ block₃ :=
      htripleBlock₃ (hpairTriple hx₁Pair)
    have hx₂Block₃ : x₂ ∈ block₃ :=
      htripleBlock₃ (hpairTriple hx₂Pair)
    have hx₁NotThird₃ : x₁ ∉ third₃ :=
      avoids_block hincident₃ hx₁Block₃
    have hx₂NotThird₃ : x₂ ∉ third₃ :=
      avoids_block hincident₃ hx₂Block₃
    have htrace₃Card := trace_card_ge_four hincident₃ hlight₃
    obtain ⟨x₃, hx₃Trace⟩ : (third₃ ∩ residual).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hx₃Third₃ : x₃ ∈ third₃ := (Finset.mem_inter.mp hx₃Trace).1
    have hx₃Residual : x₃ ∈ residual := (Finset.mem_inter.mp hx₃Trace).2
    have hx₁NeX₃ : x₁ ≠ x₃ := by
      intro h
      apply hx₁NotThird₃
      simpa [h] using hx₃Third₃
    have hx₂NeX₃ : x₂ ≠ x₃ := by
      intro h
      apply hx₂NotThird₃
      simpa [h] using hx₃Third₃
    let triple₁₂₃ : Finset (Fin n) := {x₁, x₂, x₃}
    have htriple₁₂₃Sub : triple₁₂₃ ⊆ residual := by
      intro x hx
      simp only [triple₁₂₃, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hx₁Residual
      · exact hx₂Residual
      · exact hx₃Residual
    have htriple₁₂₃Card : triple₁₂₃.card = 3 := by
      simp [triple₁₂₃, hx₁NeX₂, hx₁NeX₃,
        hx₂NeX₃]
    obtain ⟨block₄, hblock₄Bad, htripleBlock₄⟩ :=
      badResidualFourBlocks567_covers_three hresidualCard hnoStrongResidual
        htriple₁₂₃Sub htriple₁₂₃Card
    obtain ⟨third₄, hincident₄⟩ :=
      hescape.badProbe_has_incident_witness ha hb
        (by simpa [residual] using hblock₄Bad)
    have hlight₄ := light_of_incident hincident₄
    have hx₁Triple : x₁ ∈ triple₁₂₃ := by simp [triple₁₂₃]
    have hx₂Triple : x₂ ∈ triple₁₂₃ := by simp [triple₁₂₃]
    have hx₃Triple : x₃ ∈ triple₁₂₃ := by simp [triple₁₂₃]
    have hx₁Block₄ : x₁ ∈ block₄ := htripleBlock₄ hx₁Triple
    have hx₂Block₄ : x₂ ∈ block₄ := htripleBlock₄ hx₂Triple
    have hx₃Block₄ : x₃ ∈ block₄ := htripleBlock₄ hx₃Triple
    have hx₁NotThird₄ : x₁ ∉ third₄ :=
      avoids_block hincident₄ hx₁Block₄
    have hx₂NotThird₄ : x₂ ∉ third₄ :=
      avoids_block hincident₄ hx₂Block₄
    have hx₃NotThird₄ : x₃ ∉ third₄ :=
      avoids_block hincident₄ hx₃Block₄
    have hthird₁NeThird₃ : third₁ ≠ third₃ := by
      intro h
      apply hx₁NotThird₃
      simpa [h] using hx₁Third₁
    have hthird₁NeThird₄ : third₁ ≠ third₄ := by
      intro h
      apply hx₁NotThird₄
      simpa [h] using hx₁Third₁
    have hthird₂NeThird₃ : third₂ ≠ third₃ := by
      intro h
      apply hx₂NotThird₃
      simpa [h] using hx₂Third₂
    have hthird₂NeThird₄ : third₂ ≠ third₄ := by
      intro h
      apply hx₂NotThird₄
      simpa [h] using hx₂Third₂
    have hthird₃NeThird₄ : third₃ ≠ third₄ := by
      intro h
      apply hx₃NotThird₄
      simpa [h] using hx₃Third₃
    exact ⟨{
      initial₁ := hincident₁
      initial₂ := hincident₂
      initial_ne := hthirdNe
      same_occupancy := hsame
      light₁ := hlight₁
      light₂ := hlight₂
      block₃ := block₃
      block₄ := block₄
      third₃ := third₃
      third₄ := third₄
      incident₃ := hincident₃
      incident₄ := hincident₄
      light₃ := hlight₃
      light₄ := hlight₄
      x₁ := x₁
      x₂ := x₂
      x₃ := x₃
      x₁_residual := by simpa [residual] using hx₁Residual
      x₂_residual := by simpa [residual] using hx₂Residual
      x₃_residual := by simpa [residual] using hx₃Residual
      x₁_mem_third₁ := hx₁Third₁
      x₂_mem_third₂ := hx₂Third₂
      x₃_mem_third₃ := hx₃Third₃
      x₁_ne_x₂ := hx₁NeX₂
      x₁_ne_x₃ := hx₁NeX₃
      x₂_ne_x₃ := hx₂NeX₃
      x₁_mem_block₃ := hx₁Block₃
      x₂_mem_block₃ := hx₂Block₃
      x₁_mem_block₄ := hx₁Block₄
      x₂_mem_block₄ := hx₂Block₄
      x₃_mem_block₄ := hx₃Block₄
      x₁_not_mem_third₃ := hx₁NotThird₃
      x₂_not_mem_third₃ := hx₂NotThird₃
      x₁_not_mem_third₄ := hx₁NotThird₄
      x₂_not_mem_third₄ := hx₂NotThird₄
      x₃_not_mem_third₄ := hx₃NotThird₄
      third₁_ne_third₃ := hthird₁NeThird₃
      third₁_ne_third₄ := hthird₁NeThird₄
      third₂_ne_third₃ := hthird₂NeThird₃
      third₂_ne_third₄ := hthird₂NeThird₄
      third₃_ne_third₄ := hthird₃NeThird₄ }⟩

end ErdosSzekeres

end
