import ESBlueprint.B.CtxPartLimitsLe

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Strict capacity loss when a kept and removed child are separated by no active external position on the part side. The new level increases both chain and join extension at the kept child by at least one, hence decreases the corresponding cup/cap limit. Allows opposite-side separators, arbitrary other child runs, unused levels and every new maximum. Supplies the local exclusion step for a run-region potential bound with unit cup/cap capacities and unbounded outer block lengths.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_capacity_drop_in_clear_interval (σ : Ctx.Context)
  (hpositive : ∀ x l t, σ.letterAt x = Ctx.Letter.ext l t → 1 ≤ l)
  (keep : List ℕ) (s : Ctx.Side) (m p r : ℕ)
  (hp : p ∈ σ.childPositions) (hkeep : p ∈ keep)
  (hr : r ∈ σ.childPositions) (hremoved : r ∉ keep)
  (hclear : ∀ l ∈ σ.levelsOn s 0, ∀ x ∈ σ.extPositions l,
    x < min p r ∨ max p r < x) :
  let τ := σ.part keep s m
  σ.chainExt s p p + 1 ≤ τ.chainExt s p p ∧
  σ.joinExt s p p + 1 ≤ τ.joinExt s p p ∧
  (match s with
    | Ctx.Side.lower => τ.cupLimit p p ≤ σ.cupLimit p p - 1
    | Ctx.Side.upper => τ.capLimit p p ≤ σ.capLimit p p - 1) := by
  classical
  dsimp only
  let τ := σ.part keep s m
  let removed := σ.childPositions.filter (· ∉ keep)
  change σ.chainExt s p p + 1 ≤ τ.chainExt s p p ∧
    σ.joinExt s p p + 1 ≤ τ.joinExt s p p ∧
    (match s with
      | .lower => τ.cupLimit p p ≤ σ.cupLimit p p - 1
      | .upper => τ.capLimit p p ≤ σ.capLimit p p - 1)
  have hpr : p ≠ r := by
    have hP := part_letterAt_of_child σ keep s m (List.mem_range.mp (List.mem_filter.mp hp).1)
      (of_decide_eq_true (List.mem_filter.mp hp).2)
    have hR := part_letterAt_of_child σ keep s m (List.mem_range.mp (List.mem_filter.mp hr).1)
      (of_decide_eq_true (List.mem_filter.mp hr).2)
    simp only [if_pos hkeep] at hP
    simp only [if_neg hremoved] at hR
    intro h
    rw [h, hR] at hP
    cases hP
  have hrmem : r ∈ removed := by simp [removed, hr, hremoved]
  have hext : τ.extPositions 1 = removed := part_extPositions_one hpositive keep s m
  have hside : τ.sideAt 1 = s := by
    apply part_sideAt_one_of_mem hpositive keep s m (q := r)
    rw [hext]
    exact hrmem
  have hlevels (top : ℕ) : τ.levelsOn s (if top = 0 then 0 else top + 1) =
      1 :: (σ.levelsOn s top).map (· + 1) := by
    by_cases ht : top = 0
    · subst top
      exact part_levelsOn_self_zero hside
    · simpa only [if_neg ht] using part_levelsOn_self_succ hside (show 1 ≤ top by omega)
  have hlevelMem : ∀ top l, l ∈ σ.levelsOn s top → l ∈ σ.levelsOn s 0 := by
    intro top l hl
    simp only [levelsOn, List.mem_filter, decide_eq_true_eq] at hl ⊢
    exact ⟨hl.1, hl.2.1, Or.inl True.intro⟩
  have hfilters : ∀ l ∈ σ.levelsOn s 0, ∀ x y,
      min p r ≤ x → x ≤ max p r → min p r ≤ y → y ≤ max p r →
      (σ.extPositions l).filter (· < x) = (σ.extPositions l).filter (· < y) ∧
      (σ.extPositions l).filter (x < ·) = (σ.extPositions l).filter (y < ·) := by
    intro l hl x y hx0 hx1 hy0 hy1
    constructor <;> apply List.filter_congr <;> intro z hz
    · have h := hclear l hl z hz
      simp only [decide_eq_decide]
      omega
    · have h := hclear l hl z hz
      simp only [decide_eq_decide]
      omega
  have hfoldLeft : ∀ (ls : List ℕ), (∀ l ∈ ls, l ∈ σ.levelsOn s 0) →
      ∀ x y c, min p r ≤ x → x ≤ max p r → min p r ≤ y → y ≤ max p r →
      (ls.foldl (leftStep σ) (x, c)).2 = (ls.foldl (leftStep σ) (y, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons l ls ih =>
      intro hls x y c hx0 hx1 hy0 hy1
      simp only [List.foldl_cons, leftStep]
      rw [(hfilters l (hls l (by simp)) x y hx0 hx1 hy0 hy1).1]
      split
      · rfl
      · exact ih (fun n hn => hls n (by simp [hn])) x y c hx0 hx1 hy0 hy1
  have hfoldRight : ∀ (ls : List ℕ), (∀ l ∈ ls, l ∈ σ.levelsOn s 0) →
      ∀ x y c, min p r ≤ x → x ≤ max p r → min p r ≤ y → y ≤ max p r →
      (ls.foldl (rightStep σ) (x, c)).2 = (ls.foldl (rightStep σ) (y, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons l ls ih =>
      intro hls x y c hx0 hx1 hy0 hy1
      simp only [List.foldl_cons, rightStep]
      rw [(hfilters l (hls l (by simp)) x y hx0 hx1 hy0 hy1).2]
      split
      · rfl
      · exact ih (fun n hn => hls n (by simp [hn])) x y c hx0 hx1 hy0 hy1
  have hmaxWitness : ∀ (L : List ℕ) (f : List ℕ → ℕ),
      ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
    intro L f
    have hmem : f [] ∈ L.sublists.map f := List.mem_map.2 ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, hval⟩ := List.mem_map.1 (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, hval]⟩
  have hnearest :
      (∃ x, min p r ≤ x ∧ x ≤ max p r ∧ leftStep τ (p, 0) 1 = (x, 1)) ∨
      (∃ x, min p r ≤ x ∧ x ≤ max p r ∧ rightStep τ (p, 0) 1 = (x, 1)) := by
    have hsort : removed.Pairwise (· ≤ ·) := ((childPositions_pairwise σ).filter _).imp le_of_lt
    by_cases hrp : r < p
    · left
      let L := removed.filter (· < p)
      have hrL : r ∈ L := by simp [L, hrmem, hrp]
      have hne : L ≠ [] := List.ne_nil_of_mem hrL
      let x := L.getLast hne
      have hxmem : x ∈ L := List.getLast_mem hne
      have hxp : x < p := of_decide_eq_true (List.mem_filter.mp hxmem).2
      have hrx : r ≤ x := (hsort.filter _).rel_getLast hrL
      refine ⟨x, by omega, by omega, ?_⟩
      simp only [leftStep, hext]
      change (match L.getLast? with | some y => (y, 0 + 1) | none => (p, 0)) = (x, 1)
      rw [List.getLast?_eq_some_getLast hne]
    · right
      have hpr' : p < r := by omega
      let L := removed.filter (p < ·)
      have hrL : r ∈ L := by simp [L, hrmem, hpr']
      have hne : L ≠ [] := List.ne_nil_of_mem hrL
      let x := L.head hne
      have hxmem : x ∈ L := List.head_mem hne
      have hpx : p < x := of_decide_eq_true (List.mem_filter.mp hxmem).2
      have hxr : x ≤ r := (hsort.filter _).rel_head hrL
      refine ⟨x, by omega, by omega, ?_⟩
      simp only [rightStep, hext]
      change (match L.head? with | some y => (y, 0 + 1) | none => (p, 0)) = (x, 1)
      rw [List.head?_eq_some_head hne]
  have hleftMono (top : ℕ) : σ.leftExt s top p ≤ τ.leftExt s (if top = 0 then 0 else top + 1) p := by
    obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s top)
      (fun ls => (ls.foldl (leftStep σ) (p, 0)).2)
    change σ.leftExt s top p = _ at hval
    have hlspos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hl)).1
    have hsub : (ls.map (· + 1)).Sublist (τ.levelsOn s (if top = 0 then 0 else top + 1)) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s (if top = 0 then 0 else top + 1)).sublists.map
      (fun xs => (xs.foldl (leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.leftExt s (if top = 0 then 0 else top + 1) p at hv
    rw [foldl_leftStep_part_map σ keep s m ls hlspos] at hv
    rw [hval]
    exact hv
  have hrightMono (top : ℕ) : σ.rightExt s top p ≤ τ.rightExt s (if top = 0 then 0 else top + 1) p := by
    obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s top)
      (fun ls => (ls.foldl (rightStep σ) (p, 0)).2)
    change σ.rightExt s top p = _ at hval
    have hlspos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hl)).1
    have hsub : (ls.map (· + 1)).Sublist (τ.levelsOn s (if top = 0 then 0 else top + 1)) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s (if top = 0 then 0 else top + 1)).sublists.map
      (fun xs => (xs.foldl (rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.rightExt s (if top = 0 then 0 else top + 1) p at hv
    rw [foldl_rightStep_part_map σ keep s m ls hlspos] at hv
    rw [hval]
    exact hv
  have hleftGrow (top x : ℕ) (hx0 : min p r ≤ x) (hx1 : x ≤ max p r)
      (hstep : leftStep τ (p, 0) 1 = (x, 1)) :
      σ.leftExt s top p + 1 ≤ τ.leftExt s (if top = 0 then 0 else top + 1) p := by
    obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s top)
      (fun ls => (ls.foldl (leftStep σ) (p, 0)).2)
    change σ.leftExt s top p = _ at hval
    have hlspos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hl)).1
    have hlsmem : ∀ l ∈ ls, l ∈ σ.levelsOn s 0 := fun l hl =>
      hlevelMem top l ((List.mem_sublists.mp hls).subset hl)
    have hsub : (1 :: ls.map (· + 1)).Sublist (τ.levelsOn s (if top = 0 then 0 else top + 1)) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons₂ 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s (if top = 0 then 0 else top + 1)).sublists.map
      (fun xs => (xs.foldl (leftStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨1 :: ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.leftExt s (if top = 0 then 0 else top + 1) p at hv
    rw [List.foldl_cons, hstep, foldl_leftStep_part_map σ keep s m ls hlspos,
      foldl_leftStep_count σ ls x 1,
      hfoldLeft ls hlsmem x p 0 hx0 hx1 (Nat.min_le_left _ _) (Nat.le_max_left _ _)] at hv
    rw [hval]
    omega
  have hrightGrow (top x : ℕ) (hx0 : min p r ≤ x) (hx1 : x ≤ max p r)
      (hstep : rightStep τ (p, 0) 1 = (x, 1)) :
      σ.rightExt s top p + 1 ≤ τ.rightExt s (if top = 0 then 0 else top + 1) p := by
    obtain ⟨ls, hls, hval⟩ := hmaxWitness (σ.levelsOn s top)
      (fun ls => (ls.foldl (rightStep σ) (p, 0)).2)
    change σ.rightExt s top p = _ at hval
    have hlspos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
      (one_le_of_mem_levelsOn ((List.mem_sublists.mp hls).subset hl)).1
    have hlsmem : ∀ l ∈ ls, l ∈ σ.levelsOn s 0 := fun l hl =>
      hlevelMem top l ((List.mem_sublists.mp hls).subset hl)
    have hsub : (1 :: ls.map (· + 1)).Sublist (τ.levelsOn s (if top = 0 then 0 else top + 1)) := by
      rw [hlevels]
      exact ((List.mem_sublists.mp hls).map _).cons₂ 1
    have hv := le_getD_max?_of_mem (L := (τ.levelsOn s (if top = 0 then 0 else top + 1)).sublists.map
      (fun xs => (xs.foldl (rightStep τ) (p, 0)).2))
      (List.mem_map.mpr ⟨1 :: ls.map (· + 1), List.mem_sublists.mpr hsub, rfl⟩)
    change _ ≤ τ.rightExt s (if top = 0 then 0 else top + 1) p at hv
    rw [List.foldl_cons, hstep, foldl_rightStep_part_map σ keep s m ls hlspos,
      foldl_rightStep_count σ ls x 1,
      hfoldRight ls hlsmem x p 0 hx0 hx1 (Nat.min_le_left _ _) (Nat.le_max_left _ _)] at hv
    rw [hval]
    omega
  have hGrow (top : ℕ) : σ.leftExt s top p + σ.rightExt s top p + 1 ≤
      τ.leftExt s (if top = 0 then 0 else top + 1) p +
      τ.rightExt s (if top = 0 then 0 else top + 1) p := by
    rcases hnearest with ⟨x, hx0, hx1, hx⟩ | ⟨x, hx0, hx1, hx⟩
    · have hL := hleftGrow top x hx0 hx1 hx
      have hR := hrightMono top
      omega
    · have hL := hleftMono top
      have hR := hrightGrow top x hx0 hx1 hx
      omega
  have hchain : σ.chainExt s p p + 1 ≤ τ.chainExt s p p := hGrow 0
  have hjoin : σ.joinExt s p p + 1 ≤ τ.joinExt s p p := by
    have hChainLe := hchain.trans (τ.chainExt_le_joinExt s p p)
    let vals := (σ.levelsOn s 0).map
      (fun l => σ.leftExt s l p + σ.rightExt s l p + σ.maximumAt l)
    have hMax : (vals.max?).getD 0 + 1 ≤ τ.joinExt s p p := by
      cases hh : vals.max? with
      | none =>
        simp only [Option.getD_none, Nat.zero_add]
        omega
      | some v =>
        obtain ⟨l, hl, heq⟩ := List.mem_map.mp (List.max?_mem hh)
        have hl1 := (one_le_of_mem_levelsOn hl).1
        have hmem : l + 1 ∈ τ.levelsOn s 0 := by
          rw [part_levelsOn_self_zero hside]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
        have hv := le_joinExt_of_mem_levelsOn hmem p p
        have hG := hGrow l
        simp only [if_neg (by omega : l ≠ 0)] at hG
        have hM : τ.maximumAt (l + 1) = σ.maximumAt l := part_maximumAt_succ σ keep s m hl1
        rw [hM] at hv
        simp only [Option.getD_some]
        omega
    change max (σ.chainExt s p p) ((vals.max?).getD 0) + 1 ≤ _
    omega
  refine ⟨hchain, hjoin, ?_⟩
  cases s with
  | lower =>
    change min (σ.u - 1 - τ.chainExt Side.lower p p) (σ.k - 1 - τ.joinExt Side.lower p p) ≤
      min (σ.u - 1 - σ.chainExt Side.lower p p) (σ.k - 1 - σ.joinExt Side.lower p p) - 1
    omega
  | upper =>
    change min (σ.a - 1 - τ.chainExt Side.upper p p) (σ.k - 1 - τ.joinExt Side.upper p p) ≤
      min (σ.a - 1 - σ.chainExt Side.upper p p) (σ.k - 1 - σ.joinExt Side.upper p p) - 1
    omega

end ErdosSzekeres
