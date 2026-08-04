module

public import ErdosSzekeres.TurnLanguage
public import ErdosSzekeres.Decomposable

@[expose] public section

namespace ErdosSzekeres
namespace TurnLanguage

/-- Words obtained by appending one fixed turn to any language in a star. -/
def appendTurnFromStar
    (star : Finset (Finset (List Turn))) (c : Turn) : Finset (List Turn) :=
  star.biUnion fun language ↦ language.image (fun word ↦ word ++ [c])

/-- Under a constant predecessor turn, the next pair language is obtained by
appending that turn to the incoming star at its first endpoint. -/
theorem pairTurnLanguage_succ_of_constant {n : ℕ} (κ : TripleColoring n)
    (s : Finset (Fin n)) (d : ℕ) (u v : Fin n) (c : Turn)
    (huv : u < v) (hu : u ∈ s) (hv : v ∈ s)
    (hconstant : ∀ w ∈ s, w < u → RankProfile.turnOfColoring κ w u v = c) :
    pairTurnLanguage κ s (d + 1) u v =
      insert [] (appendTurnFromStar (incomingStar κ s d u) c) := by
  classical
  ext word
  rcases List.eq_nil_or_concat' word with rfl | ⟨preWord, last, rfl⟩
  · simp [mem_pairTurnLanguage_iff, hasPairTurnWord_nil_iff, huv, hu, hv,
      appendTurnFromStar]
  · rw [mem_pairTurnLanguage_iff]
    constructor
    · rintro ⟨hlength, hword⟩
      obtain ⟨_, _, w, hw, hwu, hpre, hturn⟩ :=
        (hasPairTurnWord_append_iff _ _ _ _ _ _).1 hword
      have hlast : last = c := hturn.symm.trans (hconstant w hw hwu)
      apply Finset.mem_insert.mpr
      right
      rw [appendTurnFromStar, Finset.mem_biUnion]
      refine ⟨pairTurnLanguage κ s d w u, ?_, ?_⟩
      · exact Finset.mem_image.mpr
          ⟨w, Finset.mem_filter.mpr ⟨hw, hwu⟩, rfl⟩
      · apply Finset.mem_image.mpr
        refine ⟨preWord, ?_, by rw [hlast]⟩
        exact (mem_pairTurnLanguage_iff κ s d w u preWord).2
          ⟨by simpa using hlength, hpre⟩
    · intro hmember
      have hnotnil : preWord ++ [last] ≠ [] := by simp
      have hextended : preWord ++ [last] ∈ appendTurnFromStar (incomingStar κ s d u) c :=
        (Finset.mem_insert.mp hmember).resolve_left hnotnil
      rw [appendTurnFromStar, Finset.mem_biUnion] at hextended
      obtain ⟨language, hlanguage, hwordImage⟩ := hextended
      obtain ⟨source, hsource, heq⟩ := Finset.mem_image.mp hwordImage
      obtain ⟨w, hw, hlanguageEq⟩ := Finset.mem_image.mp hlanguage
      subst language
      have hw' := Finset.mem_filter.mp hw
      have hsource' :=
        (mem_pairTurnLanguage_iff κ s d w u source).1 hsource
      have hlast : c = last := by
        have := congrArg List.getLast? heq
        simpa using this
      rw [hlast] at heq
      have hsourceEq : source = preWord := List.append_cancel_right heq
      subst source
      refine ⟨?_, ?_⟩
      · simpa using hsource'.1
      · rw [← hlast]
        exact (hasPairTurnWord_append_of_constant _ _ _ _ _ _ hconstant).2
          ⟨huv, hv, w, hw'.1, hw'.2, hsource'.2⟩

/-- A crossing pair with its first endpoint in the lower child appends a left
turn to every predecessor word. -/
theorem pairTurnLanguage_succ_of_lower_upper {n : ℕ} (κ : TripleColoring n)
    (lower upper : Finset (Fin n))
    (h : HasDeepBelowSplit κ lower upper) (d : ℕ) (u v : Fin n)
    (hu : u ∈ lower) (hv : v ∈ upper) (huv : u < v) :
    pairTurnLanguage κ (lower ∪ upper) (d + 1) u v =
      insert []
        (appendTurnFromStar (incomingStar κ (lower ∪ upper) d u) Turn.left) := by
  apply pairTurnLanguage_succ_of_constant κ (lower ∪ upper) d u v Turn.left
    huv (Finset.mem_union_left upper hu) (Finset.mem_union_right lower hv)
  intro w hw hwu
  have hdisjoint := Finset.disjoint_left.mp h.disjoint
  have huNotUpper : u ∉ upper := fun huUpper ↦ hdisjoint hu huUpper
  have hvNotLower : v ∉ lower := fun hvLower ↦ hdisjoint hvLower hv
  have hcrossing := h.crossing ⟨w, u, v, hwu, huv⟩ hw
    (Finset.mem_union_left upper hu) (Finset.mem_union_right lower hv)
    (by simp [hvNotLower]) (by simp [huNotUpper])
  simpa [RankProfile.turnOfColoring, hwu, huv, hu] using hcrossing

/-- A crossing pair with its first endpoint in the upper child appends a right
turn to every predecessor word. -/
theorem pairTurnLanguage_succ_of_upper_lower {n : ℕ} (κ : TripleColoring n)
    (lower upper : Finset (Fin n))
    (h : HasDeepBelowSplit κ lower upper) (d : ℕ) (u v : Fin n)
    (hu : u ∈ upper) (hv : v ∈ lower) (huv : u < v) :
    pairTurnLanguage κ (lower ∪ upper) (d + 1) u v =
      insert []
        (appendTurnFromStar (incomingStar κ (lower ∪ upper) d u) Turn.right) := by
  apply pairTurnLanguage_succ_of_constant κ (lower ∪ upper) d u v Turn.right
    huv (Finset.mem_union_right lower hu) (Finset.mem_union_left upper hv)
  intro w hw hwu
  have hdisjoint := Finset.disjoint_left.mp h.disjoint
  have huNotLower : u ∉ lower := fun huLower ↦ hdisjoint huLower hu
  have hvNotUpper : v ∉ upper := fun hvUpper ↦ hdisjoint hv hvUpper
  have hcrossing := h.crossing ⟨w, u, v, hwu, huv⟩ hw
    (Finset.mem_union_right lower hu) (Finset.mem_union_left upper hv)
    (by simp [huNotLower]) (by simp [hvNotUpper])
  simpa [RankProfile.turnOfColoring, hwu, huv, huNotLower] using hcrossing

/-- Equal parent incoming stars at a lower endpoint give equal crossing pair
languages to an upper endpoint. -/
theorem pairTurnLanguage_succ_lower_upper_congr {n : ℕ}
    (κ ψ : TripleColoring n) (lower upper : Finset (Fin n))
    (hκ : HasDeepBelowSplit κ lower upper)
    (hψ : HasDeepBelowSplit ψ lower upper) (d : ℕ) (u v : Fin n)
    (hu : u ∈ lower) (hv : v ∈ upper) (huv : u < v)
    (hstar : incomingStar κ (lower ∪ upper) d u =
      incomingStar ψ (lower ∪ upper) d u) :
    pairTurnLanguage κ (lower ∪ upper) (d + 1) u v =
      pairTurnLanguage ψ (lower ∪ upper) (d + 1) u v := by
  rw [pairTurnLanguage_succ_of_lower_upper κ lower upper hκ d u v hu hv huv,
    pairTurnLanguage_succ_of_lower_upper ψ lower upper hψ d u v hu hv huv,
    hstar]

/-- Equal parent incoming stars at an upper endpoint give equal crossing pair
languages to a lower endpoint. -/
theorem pairTurnLanguage_succ_upper_lower_congr {n : ℕ}
    (κ ψ : TripleColoring n) (lower upper : Finset (Fin n))
    (hκ : HasDeepBelowSplit κ lower upper)
    (hψ : HasDeepBelowSplit ψ lower upper) (d : ℕ) (u v : Fin n)
    (hu : u ∈ upper) (hv : v ∈ lower) (huv : u < v)
    (hstar : incomingStar κ (lower ∪ upper) d u =
      incomingStar ψ (lower ∪ upper) d u) :
    pairTurnLanguage κ (lower ∪ upper) (d + 1) u v =
      pairTurnLanguage ψ (lower ∪ upper) (d + 1) u v := by
  rw [pairTurnLanguage_succ_of_upper_lower κ lower upper hκ d u v hu hv huv,
    pairTurnLanguage_succ_of_upper_lower ψ lower upper hψ d u v hu hv huv,
    hstar]

end TurnLanguage
end ErdosSzekeres

end
