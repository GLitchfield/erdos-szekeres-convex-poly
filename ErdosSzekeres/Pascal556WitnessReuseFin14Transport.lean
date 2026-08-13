module

public import ErdosSzekeres.Pascal556WitnessReuseFin14TwoBase
public import ErdosSzekeres.StructuralChargingTransport

@[expose] public section

namespace ErdosSzekeres

set_option maxHeartbeats 0
set_option maxRecDepth 20000

private theorem pascal556_containsCapSet_map_restrict_to
    {m n k : ℕ} {χ : TripleColoring n} (f : Fin m ↪o Fin n)
    {source : Finset (Fin m)} {target : Finset (Fin n)}
    (hmap : ∀ i ∈ source, f i ∈ target)
    (h : ContainsCapSet (χ.restrict f) source k) :
    ContainsCapSet χ target k := by
  obtain ⟨cap, hcapSub, hcard, hcap⟩ := h
  let e : Fin k ↪o Fin m := cap.orderEmbOfFin hcard
  have heCap : IsCap (χ.restrict f) e := by
    refine ⟨e.strictMono, ?_⟩
    intro i j l hij hjl
    exact hcap _ (cap.orderEmbOfFin_mem hcard i)
      (cap.orderEmbOfFin_mem hcard j) (cap.orderEmbOfFin_mem hcard l)
  let g : Fin k ↪o Fin n := e.trans f
  have hgCap : IsCap χ g :=
    IsMonochromaticChain.map_of_restrict_eq f rfl heCap
  refine ⟨Finset.univ.image g, ?_, ?_, FinsetPolygon.IsCap.image hgCap⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hmap (e i) (hcapSub (cap.orderEmbOfFin_mem hcard i))
  · simpa using Finset.card_image_of_injective Finset.univ g.injective

private theorem pascal556_containsCapSet_image_rev_of_reverseColor
    {n k : ℕ} {χ : TripleColoring n} {source : Finset (Fin n)}
    (h : ContainsCapSet (reverseColor χ) source k) :
    ContainsCapSet χ (source.image Fin.rev) k := by
  obtain ⟨cap, hcapSub, hcard, hcap⟩ := h
  refine ⟨cap.image Fin.rev, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hcapSub hi, rfl⟩
  · exact (Finset.card_image_of_injective _ Fin.rev_injective).trans hcard
  · intro t hi hj hk
    simp only [Finset.mem_image] at hi hj hk
    obtain ⟨ri, hri, hriEq⟩ := hi
    obtain ⟨rj, hrj, hrjEq⟩ := hj
    obtain ⟨rk, hrk, hrkEq⟩ := hk
    have hri' : ri = t.i.rev := by
      apply Fin.rev_injective
      simpa [hriEq]
    have hrj' : rj = t.j.rev := by
      apply Fin.rev_injective
      simpa [hrjEq]
    have hrk' : rk = t.k.rev := by
      apply Fin.rev_injective
      simpa [hrkEq]
    have hiRev : t.i.rev ∈ cap := by simpa [hri'] using hri
    have hjRev : t.j.rev ∈ cap := by simpa [hrj'] using hrj
    have hkRev : t.k.rev ∈ cap := by simpa [hrk'] using hrk
    have hout := hcap (reverseOrderedTriple t)
      hkRev hjRev hiRev
    simpa [reverseColor, reverseOrderedTriple] using hout

private theorem pascal556_context_base_impossible
    {n : ℕ} {χ : TripleColoring n}
    {left right first singleton : Finset (Fin n)}
    (hcontext : FiveSingletonResidualProbeContext556 χ left right first singleton) :
    False := by
  classical
  rcases hcontext with
    ⟨hdisjoint, horder, htotal, hleftCap, hrightCap,
      hone, hnoCap, hnoCup, hnoStrong, _hprobe⟩
  let le : Fin left.card ↪o Fin n := left.orderEmbOfFin rfl
  let re : Fin right.card ↪o Fin n := right.orderEmbOfFin rfl
  let f0 : Fin (left.card + right.card) → Fin n := Fin.addCases le re
  have hf0 : StrictMono f0 := by
    intro i j hij
    induction i using Fin.addCases with
    | left i =>
        induction j using Fin.addCases with
        | left j =>
            simpa [f0] using le.strictMono (by simpa using hij)
        | right j =>
            simpa [f0] using horder _ (left.orderEmbOfFin_mem rfl i)
              _ (right.orderEmbOfFin_mem rfl j)
    | right i =>
        induction j using Fin.addCases with
        | left j =>
            have hval : left.card + i.val < j.val := by simpa using hij
            omega
        | right j =>
            simpa [f0] using re.strictMono (by simpa using hij)
  let fsum : Fin (left.card + right.card) ↪o Fin n :=
    OrderEmbedding.ofStrictMono f0 hf0
  let cast : Fin 14 ≃o Fin (left.card + right.card) :=
    Fin.castOrderIso htotal.symm
  let f : Fin 14 ↪o Fin n := cast.toOrderEmbedding.trans fsum
  let ψ : TripleColoring 14 := χ.restrict f
  have hfLeft (i : Fin 14) (hi : i.val < left.card) : f i ∈ left := by
    let il : Fin left.card := ⟨i.val, hi⟩
    have hcast : cast i = Fin.castAdd right.card il := by
      apply Fin.ext
      rfl
    change f0 (cast i) ∈ left
    rw [hcast]
    simp only [f0, Fin.addCases_left]
    exact left.orderEmbOfFin_mem rfl il
  have hfRight (i : Fin 14) (hi : left.card ≤ i.val) : f i ∈ right := by
    let ir : Fin right.card := ⟨i.val - left.card, by omega⟩
    have hcast : cast i = Fin.natAdd left.card ir := by
      apply Fin.ext
      simp [ir]
      omega
    change f0 (cast i) ∈ right
    rw [hcast]
    simp only [f0, Fin.addCases_right]
    exact right.orderEmbOfFin_mem rfl ir
  have hfmem (i : Fin 14) : f i ∈ left ∪ right := by
    by_cases hi : i.val < left.card
    · exact Finset.mem_union_left _ (hfLeft i hi)
    · exact Finset.mem_union_right _ (hfRight i (by omega))
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 14 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, htotal, himageCard]
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hψNoCap : ¬ContainsCapSet ψ Finset.univ 5 := by
    intro hcap
    apply hnoCap
    simpa [himage] using containsCapSet_map_restrict f hcap
  have hψNoCup : ¬ContainsCupSet ψ Finset.univ 5 := by
    intro hcup
    apply hnoCup
    simpa [himage] using containsCupSet_map_restrict f hcup
  have hψNoStrong : ¬ContainsStrongPolygonSet ψ Finset.univ 6 := by
    intro hstrong
    apply hnoStrong
    simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong
  by_cases hleftSmall : left.card ≤ 7
  · let cut : Fin 8 := ⟨left.card, by omega⟩
    have hψNoLeft :
        ¬ContainsCapSet ψ (Pascal556WitnessReuseFin14CutLeft cut) 4 := by
      intro hcap
      apply hleftCap
      exact pascal556_containsCapSet_map_restrict_to f
        (fun i hi ↦ hfLeft i (by
          simpa [Pascal556WitnessReuseFin14CutLeft, cut] using
            (Finset.mem_filter.mp hi).2)) hcap
    have hψNoRight :
        ¬ContainsCapSet ψ (Pascal556WitnessReuseFin14CutRight cut) 4 := by
      intro hcap
      apply hrightCap
      exact pascal556_containsCapSet_map_restrict_to f
        (fun i hi ↦ hfRight i (by
          simpa [Pascal556WitnessReuseFin14CutRight, cut] using
            (Finset.mem_filter.mp hi).2)) hcap
    exact pascal556WitnessReuseFin14BaseForbidden_impossible ψ cut
      ⟨hψOne, hψNoCap, hψNoCup, hψNoStrong, hψNoLeft, hψNoRight⟩
  · have hrightSmall : right.card ≤ 7 := by omega
    let cut : Fin 8 := ⟨right.card, by omega⟩
    let ρ : TripleColoring 14 := reverseColor ψ
    have hρOne : OneChangeOn ρ Finset.univ := by
      intro i j k l hij hjk hkl _ _ _ _
      have horig := hψOne (i := l.rev) (j := k.rev) (k := j.rev) (l := i.rev)
        (by simpa using hkl) (by simpa using hjk) (by simpa using hij)
        (by simp) (by simp) (by simp) (by simp)
      simpa [ρ, reverseColor, reverseOrderedTriple] using horig.reversed
    have hρNoCap : ¬ContainsCapSet ρ Finset.univ 5 := by
      intro hcap
      exact hψNoCap (containsCapSet_of_reverseColor hcap)
    have hρNoCup : ¬ContainsCupSet ρ Finset.univ 5 := by
      intro hcup
      exact hψNoCup (containsCupSet_of_reverseColor hcup)
    have hρNoStrong : ¬ContainsStrongPolygonSet ρ Finset.univ 6 := by
      intro hstrong
      exact hψNoStrong (containsStrongPolygonSet_of_reverseColor hstrong)
    have hρNoLeft :
        ¬ContainsCapSet ρ (Pascal556WitnessReuseFin14CutLeft cut) 4 := by
      intro hcap
      apply hrightCap
      apply pascal556_containsCapSet_map_restrict_to f
        (source := (Pascal556WitnessReuseFin14CutLeft cut).image Fin.rev)
      · intro i hi
        simp only [Finset.mem_image] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        apply hfRight
        have hjlt := (Finset.mem_filter.mp hj).2
        simp [Pascal556WitnessReuseFin14CutLeft, cut] at hjlt
        have hrev := j.add_rev_cast
        simpa using (show left.card ≤ (j.rev : Fin 14).val by omega)
      · exact pascal556_containsCapSet_image_rev_of_reverseColor hcap
    have hρNoRight :
        ¬ContainsCapSet ρ (Pascal556WitnessReuseFin14CutRight cut) 4 := by
      intro hcap
      apply hleftCap
      apply pascal556_containsCapSet_map_restrict_to f
        (source := (Pascal556WitnessReuseFin14CutRight cut).image Fin.rev)
      · intro i hi
        simp only [Finset.mem_image] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        apply hfLeft
        have hjge := (Finset.mem_filter.mp hj).2
        simp [Pascal556WitnessReuseFin14CutRight, cut] at hjge
        have hrev := j.add_rev_cast
        simpa using (show (j.rev : Fin 14).val < left.card by omega)
      · exact pascal556_containsCapSet_image_rev_of_reverseColor hcap
    exact pascal556WitnessReuseFin14BaseForbidden_impossible ρ cut
      ⟨hρOne, hρNoCap, hρNoCup, hρNoStrong, hρNoLeft, hρNoRight⟩

/-- The stronger target-free Fin14 contradiction proves the exact frozen
distinct-witness leaf without using its witness premise. -/
theorem twoFiveSingletonProbeWitnessesImpossible556 :
    TwoFiveSingletonProbeWitnessesImpossible556 := by
  intro n χ left right first singleton a b hcontext _ha _hb _hwitnesses
  exact pascal556_context_base_impossible hcontext

/-- The same stronger contradiction proves the exact frozen ten-fiber leaf
without using its fiber premise. -/
theorem tenProbeFiveSingletonWitnessImpossible556 :
    TenProbeFiveSingletonWitnessImpossible556 := by
  intro n χ left right first singleton a b hcontext _ha _hb _hfiber
  exact pascal556_context_base_impossible hcontext

end ErdosSzekeres

end
