import ESBlueprint.B.CtxActiveBoundaryMarkerRankUnionBound

import ESBlueprint.B.CtxNonunitChildrenExteriorOfTwoLevels
import ESBlueprint.B.CtxBoundLeOneOfClearUnitAxis
import ESBlueprint.B.CtxPartCapacityDropInClearInterval

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- A recursive cut rank budget when the part on an axis with global parameter at most four retains a child of chosen capacity at least two. With two actual indexed source levels on that axis and at least one removed source child, every fuel approximation and the full chosen-axis part bound are at most the cardinality of the source active opposite-rank union; every approximation and full complementary opposite-axis part bound are at most one. The witness may be inactive on the opposite axis. Covers arbitrary kept sets and new maxima, positive labels, repeated markers and arbitrary older histories. Nonunit survival forces every removed child into the opposite exterior, making its new level-one marker an active boundary; the complementary part is clear and unit on the chosen axis. Supplies the rank-union-plus-one estimate for the difficult nonunit branch of the singleton-end sandwich mixed-potential induction.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_cut_rank_budget_of_nonunit_part (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 4)
  (keep : List ℕ) (m n p q : ℕ)
  (hp : p ∈ (σ.part keep s m).childPositions)
  (hnonunit : 2 ≤ (match s with
    | Ctx.Side.lower => (σ.part keep s m).cupLimit p p
    | Ctx.Side.upper => (σ.part keep s m).capLimit p p))
  (hq : q ∈ σ.childPositions) (hremoved : q ∉ keep) :
  let ownPart := σ.part keep s m
  let otherPart := σ.part (σ.childPositions.filter (· ∉ keep)) t n
  let budget := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  let active := σ.childPositions.toFinset.filter
    (fun p => 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  let ranks := active.biUnion
    (fun p => Finset.Icc (σ.leftExt t 0 p + 1) (budget - σ.rightExt t 0 p))
  (∀ fuel, Ctx.Context.boundFuel fuel ownPart ≤ ranks.card) ∧ ownPart.bound ≤ ranks.card ∧
    (∀ fuel, Ctx.Context.boundFuel fuel otherPart ≤ 1) ∧ otherPart.bound ≤ 1 := by
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
  change (∀ fuel, boundFuel fuel A ≤ (ranks σ).card) ∧ A.bound ≤ (ranks σ).card ∧
    (∀ fuel, boundFuel fuel B ≤ 1) ∧ B.bound ≤ 1
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
  have hpOld : 2 ≤ C σ s p := by
    have hle := ctx_part_limits_le σ keep s m p p
    cases s <;> dsimp only [C, A] at hp2 ⊢ <;> omega
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
  obtain ⟨dir, hOutside⟩ : ∃ dir : Bool, ∀ r ∈ σ.childPositions, 2 ≤ C σ s r →
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir z r := by
    rcases ctx_nonunit_children_exterior_of_two_levels σ s N M x y hN hM hNM hNs hMs hx hy hglobal with hh | hh
    · refine ⟨true, ?_⟩
      intro r hr h2 j hj z hz
      have h2' : 2 ≤ (match s with | Side.lower => σ.cupLimit r r | Side.upper => σ.capLimit r r) := by
        cases s <;> simpa only [C] using h2
      exact hh.2 r hr h2' j hj z hz
    · refine ⟨false, ?_⟩
      intro r hr h2 j hj z hz
      have h2' : 2 ≤ (match s with | Side.lower => σ.cupLimit r r | Side.upper => σ.capLimit r r) := by
        cases s <;> simpa only [C] using h2
      exact hh.2 r hr h2' j hj z hz
  have hRemoved (r : ℕ) (hr : r ∈ σ.childPositions) (hn : r ∉ keep) :
      ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir r z := by
    intro j hj z hz
    have hj1 := (one_le_of_mem_levelsOn hj).1
    obtain ⟨hjA, hsjA, hextA⟩ := hOld j hj
    have hzA : z ∈ A.extPositions (j + 1) := by rw [hextA]; exact hz
    have hjOnA : j + 1 ∈ A.levelsOn s 0 := List.mem_filter.mpr ⟨hjA, by simp [hsjA]⟩
    have hpz := hOutside p hcp.1 hpOld j hj z hz
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
  have hOuterUnit (r : ℕ) (hr : r ∈ σ.childPositions)
      (hout : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir r z) : C σ s r ≤ 1 := by
    by_contra hn
    have h2 : 2 ≤ C σ s r := by omega
    have hxr := hOutside r hr h2 N hNOn x hx
    have hrx := hout N hNOn x hx
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hxr hrx <;> omega
  have hAfter (r : ℕ) (hr : r ∈ A.childPositions)
      (hactive : 0 < A.cupLimit r r ∧ 0 < A.capLimit r r) : Rel dir q r := by
    have hrc := (hChild keep s m r).mp hr
    have hrq : r ≠ q := by intro he; subst r; exact hremoved hrc.2
    by_contra hnot
    have hbefore : Rel dir r q := by
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hnot ⊢ <;> omega
    have hout : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j, Rel dir r z := by
      intro j hj z hz
      have hqz := hRemoved q hq hremoved j hj z hz
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hbefore hqz ⊢ <;> omega
    have hu := hOuterUnit r hrc.1 hout
    have hclear : ∀ j ∈ σ.levelsOn s 0, ∀ z ∈ σ.extPositions j,
        z < min r q ∨ max r q < z := by
      intro j hj z hz
      have hrz := hout j hj z hz
      have hqz := hRemoved q hq hremoved j hj z hz
      cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hrz hqz <;> omega
    have hd := (ctx_part_capacity_drop_in_clear_interval σ hpositive keep s m r q
      hrc.1 hrc.2 hq hremoved hclear).2.2
    cases s <;> dsimp only [C, A] at hu hactive hd <;> omega
  have hChildrenA : ∀ r ∈ A.childPositions, 0 < A.cupLimit r r ∧ 0 < A.capLimit r r →
      if !dir then r < q else q < r := by
    intro r hr ha
    have hh := hAfter r hr ha
    cases dir <;> simpa only [Rel, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] using hh
  have hYoungerA : ∀ j ∈ A.levelsOn (A.sideAt 1) 1, ∀ z ∈ A.extPositions j,
      if !dir then z < q else q < z := by simp only [levelsOn_one, List.not_mem_nil, false_implies, implies_true]
  have hSmallA : min (G A (A.sideAt 1) - 1) (A.k - A.maximumAt 1) ≤ 3 := by
    rw [hASide]
    exact (Nat.min_le_left _ _).trans (by omega)
  have hAT : A.sideAt 1 ≠ t := by rw [hASide]; exact hne
  have hBoundA := ctx_active_boundary_marker_rank_union_bound A (hPosPart keep s m)
    1 q hA1 (hNew q hq hremoved) (!dir) hChildrenA hYoungerA t hAT hSmallA
  change (∀ fuel, boundFuel fuel A ≤ (ranks A).card) ∧ A.bound ≤ (ranks A).card at hBoundA
  have hPure (r : ℕ) : A.leftExt t 0 r = σ.leftExt t 0 r ∧ A.rightExt t 0 r = σ.rightExt t 0 r :=
    ⟨(leftExt_part_other hAT r).1, (rightExt_part_other hAT r).1⟩
  have hRankSubset : ranks A ⊆ ranks σ := by
    intro z hz
    obtain ⟨r, hr, hz⟩ := Finset.mem_biUnion.mp hz
    have hra := Finset.mem_filter.mp hr
    have hrc := (hChild keep s m r).mp (List.mem_toFinset.mp hra.1)
    have hpos : 0 < A.cupLimit r r ∧ 0 < A.capLimit r r := hra.2
    have hle := ctx_part_limits_le σ keep s m r r
    have hrσ : r ∈ active σ := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hrc.1, by dsimp only [A] at hpos; omega⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hrσ, ?_⟩
    have hGAT : G A t = G σ t := by cases t <;> rfl
    simpa only [(hPure r).1, (hPure r).2, hGAT] using hz
  have hCard := Finset.card_le_card hRankSubset
  have hpNotRest : p ∉ rest := by
    intro he
    have hn : p ∉ keep := by simpa only [rest, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp he).2
    exact hn hcp.2
  have hBSide : B.sideAt 1 = t := hSide rest t n p hcp.1 hpNotRest
  have hBNotS : B.sideAt 1 ≠ s := by rw [hBSide]; exact Ne.symm hne
  have hBChild (r : ℕ) (hr : r ∈ B.childPositions) : r ∈ σ.childPositions ∧ r ∉ keep := by
    have hh := (hChild rest t n r).mp hr
    exact ⟨hh.1, by simpa only [rest, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hh.2).2⟩
  have hBUnit : ∀ r ∈ B.childPositions,
      (match s with | Side.lower => B.cupLimit r r | Side.upper => B.capLimit r r) ≤ 1 := by
    intro r hr
    have hh := hBChild r hr
    have hu := hOuterUnit r hh.1 (hRemoved r hh.1 hh.2)
    have hle := ctx_part_limits_le σ rest t n r r
    cases s <;> dsimp only [C, B] at hu ⊢ <;> omega
  have hBClear : ∀ r ∈ B.childPositions, ∀ w ∈ B.childPositions,
      ∀ j ∈ B.levelsOn s 0, ∀ z ∈ B.extPositions j, z < min r w ∨ max r w < z := by
    intro r hr w hw j hj z hz
    have hrσ := hBChild r hr
    have hwσ := hBChild w hw
    rw [show B.levelsOn s 0 = (σ.levelsOn s 0).map (· + 1) from part_levelsOn_other_zero hBNotS] at hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have hext : B.extPositions (i + 1) = σ.extPositions i :=
      part_extPositions_succ σ rest t n (one_le_of_mem_levelsOn hi).1
    rw [hext] at hz
    have hrz := hRemoved r hrσ.1 hrσ.2 i hi z hz
    have hwz := hRemoved w hwσ.1 hwσ.2 i hi z hz
    cases dir <;> simp only [Rel, Bool.false_eq_true, if_false, if_true] at hrz hwz <;> omega
  have hBoundB := ctx_bound_le_one_of_clear_unit_axis B (hPosPart rest t n) s hBUnit hBClear
  exact ⟨fun fuel => (hBoundA.1 fuel).trans hCard, hBoundA.2.trans hCard, hBoundB⟩

end ErdosSzekeres
