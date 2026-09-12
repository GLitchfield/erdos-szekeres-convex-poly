import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxSiblingMaximumUpperNormalize
import ESBlueprint.B.CtxBracketedChildrenUnitBound

set_option maxHeartbeats 8000000
set_option maxRecDepth 15000
open ErdosSzekeres.Ctx ErdosSzekeres.Ctx.Context


namespace ErdosSzekeres

/-- Bound an internally bracketed chosen part by one when an original indexed chosen maximum is at least k-4. Normalize that original maximum after taking the part: the chosen global becomes at most four, and the new level-one boundary witnesses survive. The checked bracketed-child theorem then gives the shared unit bound. Positive physical labels and an indexed level on the chosen axis with maximum at least k-4. All retained source children lie strictly between two complementary source children. The new maximum is arbitrary. No original global bound, opposite-width bound, actual occurrence at the selected old level, history-depth restriction, convexity or legal-maximum coupling is required. Physical external positions are preserved.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_large_chosen_maximum_bracketed_part_unit_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side) (N : ℕ) (hN : N ∈ σ.levels) (hNs : σ.sideAt N=s)
  (hmaximum : σ.k-4 ≤ σ.maximumAt N)
  (keep : List ℕ) (m l r : ℕ)
  (hl : l ∈ σ.childPositions) (hr : r ∈ σ.childPositions)
  (hlnot : l ∉ keep) (hrnot : r ∉ keep)
  (hinside : ∀ p ∈ σ.childPositions, p ∈ keep → l<p ∧ p<r) :
  (∀ fuel, Ctx.Context.boundFuel fuel (σ.part keep s m) ≤ 1) ∧
    (σ.part keep s m).bound ≤ 1 := by
  classical
  let α := σ.part keep s m
  have hNpos := one_le_of_mem_levels hN
  have hNα : N+1 ∈ α.levels := by
    rw [part_levels]
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨N,hN,rfl⟩)
  have hNsα : α.sideAt (N+1)=s := (part_sideAt_succ σ keep s m hNpos).trans hNs
  have hMaximum : α.maximumAt (N+1)=σ.maximumAt N := part_maximumAt_succ σ keep s m hNpos
  have hL : l ∈ α.extPositions 1 := by
    rw [part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hl,by simp [hlnot]⟩
  have hR : r ∈ α.extPositions 1 := by
    rw [part_extPositions_one hpositive]
    exact List.mem_filter.mpr ⟨hr,by simp [hrnot]⟩
  have hSide : α.sideAt 1=s := part_sideAt_one_of_mem hpositive keep s m hL
  have hPosα : ∀ p j v, α.letterAt p = Letter.ext j v → 1 ≤ j := by
    intro p j v hp
    have hpl : p<σ.word.length := by
      by_contra h
      have hh := letterAt_of_length_le α
        (show α.word.length≤p by rw [part_word_length]; omega)
      rw [hh] at hp
      cases hp
    cases he : σ.letterAt p with
    | child =>
      rw [part_letterAt_of_child σ keep s m hpl he] at hp
      split at hp
      · cases hp
      · cases hp; omega
    | ext i z =>
      rw [part_letterAt_of_ext σ keep s m hpl he] at hp
      cases hp; omega
  let ν : Context := match α.sideAt (N+1) with
    | Side.lower => {α with u:=min α.u (α.k-α.maximumAt (N+1)), maxima:=α.maxima.take N}
    | Side.upper => {α with a:=min α.a (α.k-α.maximumAt (N+1)), maxima:=α.maxima.take N}
  have hn := ctx_sibling_maximum_upper_normalize α (N+1) hNα
  have hFuel : ∀ fuel, boundFuel fuel α ≤ boundFuel fuel ν := by
    simpa only [Nat.add_sub_cancel] using hn.2.1
  have hFull : α.bound ≤ ν.bound := by simpa only [Nat.add_sub_cancel] using hn.2.2
  have hWord : ν.word=α.word := by cases hs : α.sideAt (N+1) <;> simp only [ν,hs]
  have hMaxima : ν.maxima=α.maxima.take N := by cases hs : α.sideAt (N+1) <;> simp only [ν,hs]
  have hLetter (p : ℕ) : ν.letterAt p=α.letterAt p := by simp only [letterAt,hWord]
  have hChild : ν.childPositions=α.childPositions := by simp only [childPositions,hWord,hLetter]
  have hExt (j : ℕ) : ν.extPositions j=α.extPositions j := by simp only [extPositions,hWord,hLetter]
  have hSides (j : ℕ) : ν.sideAt j=α.sideAt j := by simp only [sideAt,hExt,hLetter]
  have hPosν : ∀ p j v, ν.letterAt p=Letter.ext j v → 1≤j := by
    intro p j v hp
    rw [hLetter] at hp
    exact hPosα p j v hp
  have hLevelMem (ρ : Context) (j : ℕ) : j ∈ ρ.levels ↔ 1≤j ∧ j≤ρ.maxima.length := by
    simp only [levels,List.mem_map,List.mem_range]
    constructor
    · rintro ⟨i,hi,rfl⟩; omega
    · intro hj; exact ⟨j-1,by omega,by omega⟩
  have hOneν : 1 ∈ ν.levels := by
    apply (hLevelMem ν 1).mpr
    rw [hMaxima,List.length_take]
    have hd : α.maxima.length=σ.maxima.length+1 := by simp [α,part]
    omega
  have hGlobal : (match s with | Side.lower=>ν.u | Side.upper=>ν.a)≤4 := by
    have hc : α.k-α.maximumAt (N+1)≤4 := by
      rw [hMaximum]
      change σ.k-σ.maximumAt N≤4
      omega
    cases s <;> simp only [ν,hNsα]
    all_goals exact (Nat.min_le_right _ _).trans hc
  have hBound := (ctx_bracketed_children_unit_bound ν hPosν s 1 1 l r
    hOneν hOneν (by rw [hSides]; exact hSide) (by rw [hSides]; exact hSide)
    (by rw [hExt]; exact hL) (by rw [hExt]; exact hR) hGlobal).2
    (by
      intro p hp
      rw [hChild,part_childPositions] at hp
      have hh := List.mem_filter.mp hp
      exact hinside p hh.1 (of_decide_eq_true hh.2))
  exact ⟨fun fuel=>(hFuel fuel).trans (hBound.1 fuel),hFull.trans hBound.2⟩


end ErdosSzekeres
