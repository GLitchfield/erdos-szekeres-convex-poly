import ESBlueprint.B.CtxCutRankBudgetOfNonunitPart

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- A nonunit child retained by a chosen-axis part forces every removed source child into the opposite exterior of all old chosen markers, assuming only one actual indexed source marker and chosen global at most four. The nonunit witness may be inactive, and the kept set and two new maxima are arbitrary. The complementary opposite-axis part has every fuel approximation and its full bound controlled by its exact active opposite pure-rank union. Two-level exterior orientation is applied in the chosen part after insertion of the new level; the youngest actual chosen marker supplies the active-boundary rank estimate in the companion. Removes the exterior-companion case from the one-level separate-exterior-rank potential toward the singleton-end sandwich proof.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_nonunit_part_companion_exterior_rank_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N x : ℕ)
  (hN : N ∈ σ.levels) (hNs : σ.sideAt N = s) (hx : x ∈ σ.extPositions N)
  (hglobal : (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) s ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hnonunit : 2 ≤ (fun v : Ctx.Side => match v with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
    | Ctx.Side.upper => (σ.part keep s m).capLimit p p) s)
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let otherPart := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let active := otherPart.childPositions.toFinset.filter
    (fun r => 0 < otherPart.cupLimit r r ∧ 0 < otherPart.capLimit r r)
  let ranks := active.biUnion (fun r => Finset.Icc
    (otherPart.leftExt t 0 r + 1) (global otherPart t - 1 - otherPart.rightExt t 0 r))
  (∃ rightward : Bool,
    (∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
      if rightward then z < p else p < z) ∧
    (∀ r ∈ σ.childPositions, r ∉ keep → ∀ j ∈ σ.levelsOn s 0,
      ∀ z ∈ σ.extPositions j, if rightward then r < z else z < r)) ∧
    (∀ fuel, Ctx.Context.boundFuel fuel otherPart ≤ ranks.card) ∧ otherPart.bound ≤ ranks.card := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (r : ℕ) := match v with
    | Side.lower => ρ.cupLimit r r
    | Side.upper => ρ.capLimit r r
  let Rel (d : Bool) (a b : ℕ) : Prop := if d then a < b else b < a
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun r => 0 < ρ.cupLimit r r ∧ 0 < ρ.capLimit r r)
  let ranks (ρ : Context) := (active ρ).biUnion
    (fun r => Finset.Icc (ρ.leftExt t 0 r + 1) (G ρ t - 1 - ρ.rightExt t 0 r))
  let rest := σ.childPositions.filter (· ∉ keep)
  let A := σ.part keep s m
  let B := σ.part rest t n
  change (∃ dir : Bool,
    (∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir z p) ∧
    (∀ r ∈ σ.childPositions, r ∉ keep → ∀ j ∈ σ.levelsOn s 0,
      ∀ z ∈ σ.extPositions j, Rel dir r z)) ∧
    (∀ fuel, boundFuel fuel B ≤ (ranks B).card) ∧ B.bound ≤ (ranks B).card
  have hChild (ks : List ℕ) (v : Side) (c r : ℕ) :
      r ∈ (σ.part ks v c).childPositions ↔ r ∈ σ.childPositions ∧ r ∈ ks := by
    simp only [part_childPositions, List.mem_filter, decide_eq_true_eq]
  have hPosPart (ks : List ℕ) (v : Side) (c : ℕ) :
      ∀ r j w, (σ.part ks v c).letterAt r = Letter.ext j w → 1 ≤ j := by
    intro r j w hr
    have hrl : r < σ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (σ.part ks v c)
        (show (σ.part ks v c).word.length ≤ r by rw [part_word_length]; omega)
      rw [hn] at hr
      cases hr
    cases he : σ.letterAt r with
    | child =>
      rw [part_letterAt_of_child σ ks v c hrl he] at hr
      split at hr
      · cases hr
      · cases hr; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext σ ks v c hrl he] at hr
      cases hr; omega
  have hSide (ks : List ℕ) (v : Side) (c r : ℕ)
      (hr : r ∈ σ.childPositions) (hn : r ∉ ks) :
      (σ.part ks v c).sideAt 1 = v := by
    apply part_sideAt_one_of_mem hpositive ks v c (q := r)
    rw [part_extPositions_one hpositive ks v c]
    exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
  have hcp := (hChild keep s m p).mp hp
  have hp2 : 2 ≤ C A s p := by cases s <;> simpa only [C, A] using hnonunit
  have hG : G σ s ≤ 4 := by cases s <;> simpa only [G] using hglobal
  have hGA : G A s ≤ 4 := hG
  have hA1 : 1 ∈ A.levels := by simp only [A, part_levels, List.mem_cons, true_or]
  have hASide : A.sideAt 1 = s := hSide keep s m q hq hremoved
  have hNew (r : ℕ) (hr : r ∈ σ.childPositions) (hn : r ∉ keep) : r ∈ A.extPositions 1 := by
    rw [show A.extPositions 1 = σ.childPositions.filter (· ∉ keep) from
      part_extPositions_one hpositive keep s m]
    exact List.mem_filter.mpr ⟨hr, by simp [hn]⟩
  have hOld (j : ℕ) (hj : j ∈ σ.levelsOn s 0) :
      j + 1 ∈ A.levels ∧ A.sideAt (j + 1) = s ∧ A.extPositions (j + 1) = σ.extPositions j := by
    have hh := one_le_of_mem_levelsOn hj
    refine ⟨?_, ?_, part_extPositions_succ σ keep s m hh.1⟩
    · rw [show A.levels = 1 :: σ.levels.map (· + 1) from part_levels σ keep s m]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, rfl⟩)
    · rw [show A.sideAt (j + 1) = σ.sideAt j from part_sideAt_succ σ keep s m hh.1]
      exact hh.2.2
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  obtain ⟨dir, hOutside⟩ : ∃ dir : Bool,
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir z p := by
    obtain ⟨hNA, hNsA, hExtA⟩ := hOld N hNOn
    have hxA : x ∈ A.extPositions (N + 1) := by rw [hExtA]; exact hx
    have h0 := ctx_nonunit_children_exterior_of_two_levels A s 1 (N + 1) q x
      hA1 hNA (by have := (one_le_of_mem_levelsOn hNOn).1; omega)
      hASide hNsA (hNew q hq hremoved) hxA
      (by cases s <;> simpa only [G] using hGA)
    rcases h0 with hh | hh
    · refine ⟨true, ?_⟩
      intro j hj z hz
      obtain ⟨hjA, hsjA, hextA⟩ := hOld j hj
      have hjOnA : j + 1 ∈ A.levelsOn s 0 := List.mem_filter.mpr ⟨hjA, by simp [hsjA]⟩
      exact hh.2 p hp (by cases s <;> simpa only [C] using hp2)
        (j + 1) hjOnA z (by rw [hextA]; exact hz)
    · refine ⟨false, ?_⟩
      intro j hj z hz
      obtain ⟨hjA, hsjA, hextA⟩ := hOld j hj
      have hjOnA : j + 1 ∈ A.levelsOn s 0 := List.mem_filter.mpr ⟨hjA, by simp [hsjA]⟩
      exact hh.2 p hp (by cases s <;> simpa only [C] using hp2)
        (j + 1) hjOnA z (by rw [hextA]; exact hz)
  have hRemoved (r : ℕ) (hr : r ∈ σ.childPositions) (hn : r ∉ keep) :
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir r z := by
    intro j hj z hz
    have hj1 := (one_le_of_mem_levelsOn hj).1
    obtain ⟨hjA, hsjA, hextA⟩ := hOld j hj
    have hzA : z ∈ A.extPositions (j + 1) := by rw [hextA]; exact hz
    have hjOnA : j + 1 ∈ A.levelsOn s 0 := List.mem_filter.mpr ⟨hjA, by simp [hsjA]⟩
    have hpz := hOutside j hj z hz
    have hglobalA : (match s with | Side.lower => A.u | Side.upper => A.a) ≤ 4 := by
      cases s <;> simpa only [G] using hGA
    have hp2' : 2 ≤ (match s with | Side.lower => A.cupLimit p p | Side.upper => A.capLimit p p) := by
      cases s <;> simpa only [C] using hp2
    rcases ctx_nonunit_children_exterior_of_two_levels A s 1 (j + 1) r z hA1 hjA
      (by omega) hASide hsjA (hNew r hr hn) hzA hglobalA with hh | hh
    · have hzp := hh.2 p hp hp2' (j + 1) hjOnA z hzA
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hpz ⊢ <;> omega
    · have hpz' := hh.2 p hp hp2' (j + 1) hjOnA z hzA
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hpz ⊢ <;> omega
  have hpNotRest : p ∉ rest := by
    intro he
    have hn : p ∉ keep := by simpa only [rest, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp he).2
    exact hn hcp.2
  have hBSide : B.sideAt 1 = t := hSide rest t n p hcp.1 hpNotRest
  have hBNotS : B.sideAt 1 ≠ s := by rw [hBSide]; exact Ne.symm hne
  have hBChild (r : ℕ) (hr : r ∈ B.childPositions) : r ∈ σ.childPositions ∧ r ∉ keep := by
    have hh := (hChild rest t n r).mp hr
    exact ⟨hh.1, by simpa only [rest, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hh.2).2⟩
  have hBExterior (r : ℕ) (hr : r ∈ B.childPositions) :
      ∀ j ∈ B.levelsOn s 0, ∀ z ∈ B.extPositions j, Rel dir r z := by
    intro j hj z hz
    rw [show B.levelsOn s 0 = (σ.levelsOn s 0).map (· + 1) from part_levelsOn_other_zero hBNotS] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have hext : B.extPositions (i + 1) = σ.extPositions i :=
      part_extPositions_succ σ rest t n (one_le_of_mem_levelsOn hi).1
    rw [hext] at hz
    have hh := hBChild r hr
    exact hRemoved r hh.1 hh.2 i hi z hz
  have hex : ∃ j : ℕ, j ∈ B.levelsOn s 0 ∧ ∃ z, z ∈ B.extPositions j := by
    refine ⟨N + 1, ?_, x, ?_⟩
    · rw [show B.levelsOn s 0 = (σ.levelsOn s 0).map (· + 1) from part_levelsOn_other_zero hBNotS]
      exact List.mem_map.mpr ⟨N, hNOn, rfl⟩
    · rw [show B.extPositions (N + 1) = σ.extPositions N from
        part_extPositions_succ σ rest t n (one_le_of_mem_levelsOn hNOn).1]
      exact hx
  let L := Nat.find hex
  have hLOn : L ∈ B.levelsOn s 0 := (Nat.find_spec hex).1
  obtain ⟨z, hz⟩ := (Nat.find_spec hex).2
  have hL : L ∈ B.levels := (List.mem_filter.mp hLOn).1
  have hL1 : 1 ≤ L := (one_le_of_mem_levelsOn hLOn).1
  have hLSide : B.sideAt L = s := (one_le_of_mem_levelsOn hLOn).2.2
  have hChildren : ∀ r ∈ B.childPositions, 0 < B.cupLimit r r ∧ 0 < B.capLimit r r →
      if dir then r < z else z < r := by
    intro r hr _
    exact hBExterior r hr L hLOn z hz
  have hYounger : ∀ j ∈ B.levelsOn (B.sideAt L) L, ∀ w ∈ B.extPositions j,
      if dir then w < z else z < w := by
    intro j hj w hw
    rw [hLSide] at hj
    have hj' := hj
    simp only [levelsOn, List.mem_filter, decide_eq_true_eq] at hj'
    have hj0 : j ∈ B.levelsOn s 0 := List.mem_filter.mpr ⟨hj'.1, by simp [hj'.2.1]⟩
    have hmin : L ≤ j := Nat.find_min' hex ⟨hj0, w, hw⟩
    have hlt := hj'.2.2
    omega
  have hSmall : min (G B (B.sideAt L) - 1) (B.k - B.maximumAt L) ≤ 3 := by
    rw [hLSide]
    have hGB : G B s ≤ 4 := hG
    exact (Nat.min_le_left _ _).trans (by omega)
  have hBT : B.sideAt L ≠ t := by rw [hLSide]; exact hne
  have hBoundB := ctx_active_boundary_marker_rank_union_bound B (hPosPart rest t n)
    L z hL hz dir hChildren hYounger t hBT hSmall
  have hRanks : (∀ fuel, boundFuel fuel B ≤ (ranks B).card) ∧ B.bound ≤ (ranks B).card := by
    cases t <;> simpa only [ranks, active, G] using hBoundB
  exact ⟨⟨dir, hOutside, hRemoved⟩, hRanks⟩


end ErdosSzekeres
