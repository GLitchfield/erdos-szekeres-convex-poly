module

public import ErdosSzekeres.Mixed567AllOrderWitnessA
public import ErdosSzekeres.Mixed567AllOrderWitnessB
public import ErdosSzekeres.Mixed567AllOrderWitnessD

@[expose] public section

/-!
# Structural transport for the all-order mixed state-567 certificate

The label/carrier extraction and the three witness pairs are compiled in small
opaque modules.  This module only assembles them, handles carrier transposition,
and exposes the exact public consumer of the finite theorem.
-/

namespace ErdosSzekeres

private theorem shortFirstMixed567Labelling {n : ℕ}
    {χ : TripleColoring n} {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem : IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfirstCard : first.card = 6) (hsecondCard : second.card = 6)
    (hcarrierDisjoint : Disjoint first second)
    (hnormal : IsShortFirstMixedOmissionNormalForm567 first second witnesses) :
    Nonempty (Mixed567Labelling first second witnesses) := by
  classical
  obtain ⟨data⟩ := shortFirstMixed567Data hfirstCard hsecondCard
    hcarrierDisjoint hnormal
  have hA := shortFirstMixed567WitnessA hsystem data
  have hB := shortFirstMixed567WitnessB hsystem data
  have hD := shortFirstMixed567WitnessD hsystem data
  exact ⟨{
    embed := data.embed
    carrier_image := by
      simpa [Mixed567ShortFirstData.embed] using data.carrier_image
    A0_mem := hA.1
    A1_mem := hA.2
    B0_mem := hB.1
    B1_mem := hB.2
    D0_mem := hD.1
    D1_mem := hD.2 }⟩

private theorem shortSecondMixed567Labelling {n : ℕ}
    {χ : TripleColoring n} {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem : IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfirstCard : first.card = 6) (hsecondCard : second.card = 6)
    (hcarrierDisjoint : Disjoint first second)
    (hnormal : IsShortSecondMixedOmissionNormalForm567 first second witnesses) :
    Nonempty (Mixed567Labelling first second witnesses) := by
  have hsystemSwapped :
      IsCarrierOnlyOmissionRectangleSystem567 χ second first witnesses := by
    refine ⟨?_, ?_, ?_⟩
    · intro third hthird
      have hnormalThird := hsystem.1 third hthird
      rcases hnormalThird with
        ⟨hcard, hstrong, hsub, hoccupancy, hfirstPos, hfirstLe,
          hsecondPos, hsecondLe, hsum, hprofile⟩
      refine ⟨hcard, hstrong, ?_, ?_, hsecondPos, hsecondLe,
        hfirstPos, hfirstLe, by omega, ?_⟩
      · simpa [Finset.union_comm] using hsub
      · exact ⟨hoccupancy.2, hoccupancy.1⟩
      · rcases hprofile with h | h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
        · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
        · exact Or.inl ⟨h.2, h.1⟩
    · intro b hb a ha
      obtain ⟨third, hthird, hpair⟩ := hsystem.2.1 a ha b hb
      refine ⟨third, hthird, ?_⟩
      have hdata := Finset.mem_product.mp hpair
      exact Finset.mem_product.mpr ⟨hdata.2, hdata.1⟩
    · intro third1 hthird1 third2 hthird2 hne
      have hdisjoint := hsystem.2.2 third1 hthird1 third2 hthird2 hne
      apply Finset.disjoint_left.mpr
      intro pair hpair1 hpair2
      obtain ⟨b, a⟩ := pair
      have hdata1 := Finset.mem_product.mp hpair1
      have hdata2 := Finset.mem_product.mp hpair2
      have hmem1 :
          (a, b) ∈ CarrierOnlyOmissionRectangle567 first second third1 :=
        Finset.mem_product.mpr ⟨hdata1.2, hdata1.1⟩
      have hmem2 :
          (a, b) ∈ CarrierOnlyOmissionRectangle567 first second third2 :=
        Finset.mem_product.mpr ⟨hdata2.2, hdata2.1⟩
      exact (Finset.disjoint_left.mp hdisjoint) hmem1 hmem2
  obtain ⟨swapped⟩ := shortFirstMixed567Labelling hsystemSwapped
    hsecondCard hfirstCard hcarrierDisjoint.symm hnormal
  exact ⟨{
    embed := swapped.embed
    carrier_image := by simpa [Finset.union_comm] using swapped.carrier_image
    A0_mem := swapped.A0_mem
    A1_mem := swapped.A1_mem
    B0_mem := swapped.B0_mem
    B1_mem := swapped.B1_mem
    D0_mem := swapped.D0_mem
    D1_mem := swapped.D1_mem }⟩

/-- The structural normal-form consumer, parameterized by the finite theorem. -/
theorem mixedCarrierOnlyOmissionNormalForm_forces_target567_of_finite
    (hfinite : Mixed567FiniteTheorem)
    {n : ℕ} {χ : TripleColoring n}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hsystem : IsCarrierOnlyOmissionRectangleSystem567 χ first second witnesses)
    (hfirstCard : first.card = 6) (hsecondCard : second.card = 6)
    (hcarrierDisjoint : Disjoint first second)
    (hOne : OneChangeOn χ (first ∪ second))
    (hnormal :
      IsShortFirstMixedOmissionNormalForm567 first second witnesses ∨
        IsShortSecondMixedOmissionNormalForm567 first second witnesses) :
    ContainsTarget567 χ (first ∪ second) := by
  classical
  have hlabelling := hnormal.elim
    (shortFirstMixed567Labelling hsystem hfirstCard hsecondCard hcarrierDisjoint)
    (shortSecondMixed567Labelling hsystem hfirstCard hsecondCard hcarrierDisjoint)
  let labelling := Classical.choice hlabelling
  have hnormalized := hsystem.1
  have hA0 := (hnormalized _ labelling.A0_mem).2.1
  have hA1 := (hnormalized _ labelling.A1_mem).2.1
  have hB0 := (hnormalized _ labelling.B0_mem).2.1
  have hB1 := (hnormalized _ labelling.B1_mem).2.1
  have hD0 := (hnormalized _ labelling.D0_mem).2.1
  have hD1 := (hnormalized _ labelling.D1_mem).2.1
  rw [← labelling.carrier_image] at hOne ⊢
  exact hfinite χ labelling.embed hOne hA0 hA1 hB0 hB1 hD0 hD1

end ErdosSzekeres

end
