import ErdosSzekeres.DecomposableContextLemmas

namespace ErdosSzekeres

namespace Ctx
namespace Context

/-! ### The extension folds, named -/

/-- The step of `leftExt`: move the end to the rightmost letter of the level left of it. -/
def leftStep (σ : Context) : ℕ × ℕ → ℕ → ℕ × ℕ := fun (endPos, count) l =>
  match ((σ.extPositions l).filter (· < endPos)).getLast? with
  | some x => (x, count + 1)
  | none => (endPos, count)

/-- The step of `rightExt`. -/
def rightStep (σ : Context) : ℕ × ℕ → ℕ → ℕ × ℕ := fun (endPos, count) l =>
  match ((σ.extPositions l).filter (endPos < ·)).head? with
  | some x => (x, count + 1)
  | none => (endPos, count)

theorem leftExt_eq (σ : Context) (s : Side) (top p : ℕ) :
    σ.leftExt s top p =
      (((σ.levelsOn s top).sublists.map fun ls => (ls.foldl (leftStep σ) (p, 0)).2).max?).getD 0 := rfl

theorem rightExt_eq (σ : Context) (s : Side) (top p : ℕ) :
    σ.rightExt s top p =
      (((σ.levelsOn s top).sublists.map fun ls => (ls.foldl (rightStep σ) (p, 0)).2).max?).getD 0 := rfl

theorem leftStep_count (σ : Context) (e c l : ℕ) :
    leftStep σ (e, c) l = ((leftStep σ (e, 0) l).1, c + (leftStep σ (e, 0) l).2) := by
  simp only [leftStep]
  rcases h : ((σ.extPositions l).filter (· < e)).getLast? with _ | x <;> simp

theorem rightStep_count (σ : Context) (e c l : ℕ) :
    rightStep σ (e, c) l = ((rightStep σ (e, 0) l).1, c + (rightStep σ (e, 0) l).2) := by
  simp only [rightStep]
  rcases h : ((σ.extPositions l).filter (e < ·)).head? with _ | x <;> simp

theorem foldl_leftStep_count (σ : Context) (ls : List ℕ) :
    ∀ e c, (ls.foldl (leftStep σ) (e, c)).2 = c + (ls.foldl (leftStep σ) (e, 0)).2 := by
  induction ls with
  | nil => intro e c; simp
  | cons l ls ih =>
    intro e c
    simp only [List.foldl_cons]
    rw [leftStep_count σ e c l]
    rcases h : leftStep σ (e, 0) l with ⟨e', c'⟩
    rw [ih e' (c + c'), ih e' c']
    omega

theorem foldl_rightStep_count (σ : Context) (ls : List ℕ) :
    ∀ e c, (ls.foldl (rightStep σ) (e, c)).2 = c + (ls.foldl (rightStep σ) (e, 0)).2 := by
  induction ls with
  | nil => intro e c; simp
  | cons l ls ih =>
    intro e c
    simp only [List.foldl_cons]
    rw [rightStep_count σ e c l]
    rcases h : rightStep σ (e, 0) l with ⟨e', c'⟩
    rw [ih e' (c + c'), ih e' c']
    omega

/-! ### Levels and letters of a part, continued -/

theorem part_levels (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
    (σ.part keep s m).levels = 1 :: σ.levels.map (· + 1) := by
  simp only [Context.levels, part_maxima, List.length_cons, List.range_succ_eq_map, List.map_cons,
    List.map_map, zero_add]

theorem one_le_of_mem_levels {σ : Context} {l : ℕ} (h : l ∈ σ.levels) : 1 ≤ l := by
  simp only [Context.levels, List.mem_map, List.mem_range] at h
  obtain ⟨i, _, rfl⟩ := h
  omega

/-- With no level-zero letters, the level-one letters of a part are the child letters not kept. -/
theorem part_extPositions_one {σ : Context}
    (hlet : ∀ p l s', σ.letterAt p = Letter.ext l s' → 1 ≤ l) (keep : List ℕ) (s : Side) (m : ℕ) :
    (σ.part keep s m).extPositions 1 = σ.childPositions.filter (· ∉ keep) := by
  unfold Context.extPositions Context.childPositions
  rw [part_word_length, List.filter_filter]
  apply List.filter_congr
  intro p hp
  rw [List.mem_range] at hp
  rcases hσ : σ.letterAt p with _ | ⟨l₀, s₀⟩
  · rw [part_letterAt_of_child σ keep s m hp hσ]
    by_cases hmem : p ∈ keep <;> simp [hmem]
  · rw [part_letterAt_of_ext σ keep s m hp hσ]
    have := hlet p l₀ s₀ hσ
    simp
    omega

theorem part_levelsOn_self_zero {σ : Context} {keep : List ℕ} {s : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 = s) :
    (σ.part keep s m).levelsOn s 0 = 1 :: (σ.levelsOn s 0).map (· + 1) := by
  unfold Context.levelsOn
  rw [part_levels, List.filter_cons, if_pos (by simp [hside]), List.filter_map]
  congr 2
  apply List.filter_congr
  intro l hl
  have h1 := one_le_of_mem_levels hl
  simp [Function.comp, part_sideAt_succ σ keep s m h1]

theorem part_levelsOn_self_succ {σ : Context} {keep : List ℕ} {s : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 = s) {N : ℕ} (hN : 1 ≤ N) :
    (σ.part keep s m).levelsOn s (N + 1) = 1 :: (σ.levelsOn s N).map (· + 1) := by
  unfold Context.levelsOn
  rw [part_levels, List.filter_cons, if_pos (by simp [hside]; omega), List.filter_map]
  congr 2
  apply List.filter_congr
  intro l hl
  have h1 := one_le_of_mem_levels hl
  simp only [Function.comp, part_sideAt_succ σ keep s m h1, decide_eq_decide]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by omega⟩

theorem part_levelsOn_other_zero {σ : Context} {keep : List ℕ} {s s' : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 ≠ s') :
    (σ.part keep s m).levelsOn s' 0 = (σ.levelsOn s' 0).map (· + 1) := by
  unfold Context.levelsOn
  rw [part_levels, List.filter_cons, if_neg (by simp [hside]), List.filter_map]
  congr 1
  apply List.filter_congr
  intro l hl
  have h1 := one_le_of_mem_levels hl
  simp [Function.comp, part_sideAt_succ σ keep s m h1]

theorem part_levelsOn_other_succ {σ : Context} {keep : List ℕ} {s s' : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 ≠ s') {N : ℕ} (hN : 1 ≤ N) :
    (σ.part keep s m).levelsOn s' (N + 1) = (σ.levelsOn s' N).map (· + 1) := by
  unfold Context.levelsOn
  rw [part_levels, List.filter_cons, if_neg (by simp [hside]), List.filter_map]
  congr 1
  apply List.filter_congr
  intro l hl
  have h1 := one_le_of_mem_levels hl
  simp only [Function.comp, part_sideAt_succ σ keep s m h1, decide_eq_decide]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by omega⟩

theorem part_maximumAt_succ (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (σ.part keep s m).maximumAt (N + 1) = σ.maximumAt N := by
  simp only [Context.maximumAt, part_maxima]
  rcases N with _ | N
  · omega
  · simp

theorem part_maximumAt_one (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
    (σ.part keep s m).maximumAt 1 = m := by
  simp [Context.maximumAt, part_maxima]

theorem leftStep_part_succ (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) (st : ℕ × ℕ) {l : ℕ}
    (hl : 1 ≤ l) : leftStep (σ.part keep s m) st (l + 1) = leftStep σ st l := by
  rcases st with ⟨e, c⟩
  unfold leftStep
  rw [part_extPositions_succ σ keep s m hl]

theorem rightStep_part_succ (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) (st : ℕ × ℕ) {l : ℕ}
    (hl : 1 ≤ l) : rightStep (σ.part keep s m) st (l + 1) = rightStep σ st l := by
  rcases st with ⟨e, c⟩
  unfold rightStep
  rw [part_extPositions_succ σ keep s m hl]

theorem foldl_leftStep_part_map (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) (ls : List ℕ)
    (hls : ∀ l ∈ ls, 1 ≤ l) : ∀ st, (ls.map (· + 1)).foldl (leftStep (σ.part keep s m)) st =
      ls.foldl (leftStep σ) st := by
  induction ls with
  | nil => intro st; rfl
  | cons l ls ih =>
    intro st
    simp only [List.map_cons, List.foldl_cons]
    rw [leftStep_part_succ σ keep s m st (hls l (List.mem_cons_self ..))]
    exact ih (fun l' hl' => hls l' (List.mem_cons.2 (Or.inr hl'))) _

theorem foldl_rightStep_part_map (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) (ls : List ℕ)
    (hls : ∀ l ∈ ls, 1 ≤ l) : ∀ st, (ls.map (· + 1)).foldl (rightStep (σ.part keep s m)) st =
      ls.foldl (rightStep σ) st := by
  induction ls with
  | nil => intro st; rfl
  | cons l ls ih =>
    intro st
    simp only [List.map_cons, List.foldl_cons]
    rw [rightStep_part_succ σ keep s m st (hls l (List.mem_cons_self ..))]
    exact ih (fun l' hl' => hls l' (List.mem_cons.2 (Or.inr hl'))) _

/-- Every left fold of a part over its own-side levels is bounded by the parent's left
extension, either from the same start or, after one step through the new level one, from
the position `x` of a sibling letter left of the start. -/
theorem foldl_leftStep_part_le {σ : Context} {keep : List ℕ} {s : Side} {m : ℕ} {L₀ : List ℕ}
    (hL₀ : ∀ l ∈ L₀, 1 ≤ l) (p : ℕ) {ls : List ℕ} (hls : ls ∈ (1 :: L₀.map (· + 1)).sublists) :
    (ls.foldl (leftStep (σ.part keep s m)) (p, 0)).2 ≤
        ((L₀.sublists.map fun ls => (ls.foldl (leftStep σ) (p, 0)).2).max?).getD 0 ∨
      ∃ x ∈ (σ.part keep s m).extPositions 1, x < p ∧
        (ls.foldl (leftStep (σ.part keep s m)) (p, 0)).2 ≤
          1 + ((L₀.sublists.map fun ls => (ls.foldl (leftStep σ) (x, 0)).2).max?).getD 0 := by
  rw [List.mem_sublists, List.sublist_cons_iff] at hls
  rcases hls with hls | ⟨r, rfl, hr⟩
  · obtain ⟨ls₀, hls₀, rfl⟩ := List.sublist_map_iff.1 hls
    left
    rw [foldl_leftStep_part_map σ keep s m ls₀ (fun l hl => hL₀ l (hls₀.subset hl))]
    exact le_getD_max?_of_mem (List.mem_map.2 ⟨ls₀, List.mem_sublists.2 hls₀, rfl⟩)
  · obtain ⟨ls₀, hls₀, rfl⟩ := List.sublist_map_iff.1 hr
    simp only [List.foldl_cons]
    have hstep : leftStep (σ.part keep s m) (p, 0) 1 =
        match (((σ.part keep s m).extPositions 1).filter (· < p)).getLast? with
        | some x => (x, 1)
        | none => (p, 0) := rfl
    rw [hstep]
    rcases hlast : (((σ.part keep s m).extPositions 1).filter (· < p)).getLast? with _ | x
    · left
      simp only
      rw [foldl_leftStep_part_map σ keep s m ls₀ (fun l hl => hL₀ l (hls₀.subset hl))]
      exact le_getD_max?_of_mem (List.mem_map.2 ⟨ls₀, List.mem_sublists.2 hls₀, rfl⟩)
    · right
      have hx := List.mem_of_mem_getLast? (Option.mem_def.2 hlast)
      rw [List.mem_filter, decide_eq_true_eq] at hx
      refine ⟨x, hx.1, hx.2, ?_⟩
      simp only
      rw [foldl_leftStep_part_map σ keep s m ls₀ (fun l hl => hL₀ l (hls₀.subset hl)),
        foldl_leftStep_count σ ls₀ x 1]
      exact Nat.add_le_add_left (le_getD_max?_of_mem
        (L := L₀.sublists.map fun ls => (ls.foldl (leftStep σ) (x, 0)).2)
        (List.mem_map.2 ⟨ls₀, List.mem_sublists.2 hls₀, rfl⟩)) 1

theorem foldl_rightStep_part_le {σ : Context} {keep : List ℕ} {s : Side} {m : ℕ} {L₀ : List ℕ}
    (hL₀ : ∀ l ∈ L₀, 1 ≤ l) (p : ℕ) {ls : List ℕ} (hls : ls ∈ (1 :: L₀.map (· + 1)).sublists) :
    (ls.foldl (rightStep (σ.part keep s m)) (p, 0)).2 ≤
        ((L₀.sublists.map fun ls => (ls.foldl (rightStep σ) (p, 0)).2).max?).getD 0 ∨
      ∃ x ∈ (σ.part keep s m).extPositions 1, p < x ∧
        (ls.foldl (rightStep (σ.part keep s m)) (p, 0)).2 ≤
          1 + ((L₀.sublists.map fun ls => (ls.foldl (rightStep σ) (x, 0)).2).max?).getD 0 := by
  rw [List.mem_sublists, List.sublist_cons_iff] at hls
  rcases hls with hls | ⟨r, rfl, hr⟩
  · obtain ⟨ls₀, hls₀, rfl⟩ := List.sublist_map_iff.1 hls
    left
    rw [foldl_rightStep_part_map σ keep s m ls₀ (fun l hl => hL₀ l (hls₀.subset hl))]
    exact le_getD_max?_of_mem (List.mem_map.2 ⟨ls₀, List.mem_sublists.2 hls₀, rfl⟩)
  · obtain ⟨ls₀, hls₀, rfl⟩ := List.sublist_map_iff.1 hr
    simp only [List.foldl_cons]
    have hstep : rightStep (σ.part keep s m) (p, 0) 1 =
        match (((σ.part keep s m).extPositions 1).filter (p < ·)).head? with
        | some x => (x, 1)
        | none => (p, 0) := rfl
    rw [hstep]
    rcases hhead : (((σ.part keep s m).extPositions 1).filter (p < ·)).head? with _ | x
    · left
      simp only
      rw [foldl_rightStep_part_map σ keep s m ls₀ (fun l hl => hL₀ l (hls₀.subset hl))]
      exact le_getD_max?_of_mem (List.mem_map.2 ⟨ls₀, List.mem_sublists.2 hls₀, rfl⟩)
    · right
      have hx := List.mem_of_mem_head? (Option.mem_def.2 hhead)
      rw [List.mem_filter, decide_eq_true_eq] at hx
      refine ⟨x, hx.1, hx.2, ?_⟩
      simp only
      rw [foldl_rightStep_part_map σ keep s m ls₀ (fun l hl => hL₀ l (hls₀.subset hl)),
        foldl_rightStep_count σ ls₀ x 1]
      exact Nat.add_le_add_left (le_getD_max?_of_mem
        (L := L₀.sublists.map fun ls => (ls.foldl (rightStep σ) (x, 0)).2)
        (List.mem_map.2 ⟨ls₀, List.mem_sublists.2 hls₀, rfl⟩)) 1

/-- The left extension of a part on the other side equals the parent's. -/
theorem leftExt_part_other {σ : Context} {keep : List ℕ} {s s' : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 ≠ s') (p : ℕ) :
    (σ.part keep s m).leftExt s' 0 p = σ.leftExt s' 0 p ∧
      ∀ N, 1 ≤ N → (σ.part keep s m).leftExt s' (N + 1) p = σ.leftExt s' N p := by
  have key : ∀ L₀ : List ℕ, (∀ l ∈ L₀, 1 ≤ l) →
      (((L₀.map (· + 1)).sublists.map fun ls => (ls.foldl (leftStep (σ.part keep s m)) (p, 0)).2).max?).getD 0 =
        ((L₀.sublists.map fun ls => (ls.foldl (leftStep σ) (p, 0)).2).max?).getD 0 := by
    intro L₀ hL₀
    rw [List.sublists_map, List.map_map]
    congr 2
    apply List.map_congr_left
    intro ls hls
    simp only [Function.comp]
    rw [foldl_leftStep_part_map σ keep s m ls (fun l hl => hL₀ l ((List.mem_sublists.1 hls).subset hl))]
  refine ⟨?_, fun N hN => ?_⟩
  · rw [leftExt_eq, leftExt_eq, part_levelsOn_other_zero hside]
    exact key _ fun l hl => (one_le_of_mem_levelsOn hl).1
  · rw [leftExt_eq, leftExt_eq, part_levelsOn_other_succ hside hN]
    exact key _ fun l hl => (one_le_of_mem_levelsOn hl).1

theorem rightExt_part_other {σ : Context} {keep : List ℕ} {s s' : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 ≠ s') (p : ℕ) :
    (σ.part keep s m).rightExt s' 0 p = σ.rightExt s' 0 p ∧
      ∀ N, 1 ≤ N → (σ.part keep s m).rightExt s' (N + 1) p = σ.rightExt s' N p := by
  have key : ∀ L₀ : List ℕ, (∀ l ∈ L₀, 1 ≤ l) →
      (((L₀.map (· + 1)).sublists.map fun ls => (ls.foldl (rightStep (σ.part keep s m)) (p, 0)).2).max?).getD 0 =
        ((L₀.sublists.map fun ls => (ls.foldl (rightStep σ) (p, 0)).2).max?).getD 0 := by
    intro L₀ hL₀
    rw [List.sublists_map, List.map_map]
    congr 2
    apply List.map_congr_left
    intro ls hls
    simp only [Function.comp]
    rw [foldl_rightStep_part_map σ keep s m ls (fun l hl => hL₀ l ((List.mem_sublists.1 hls).subset hl))]
  refine ⟨?_, fun N hN => ?_⟩
  · rw [rightExt_eq, rightExt_eq, part_levelsOn_other_zero hside]
    exact key _ fun l hl => (one_le_of_mem_levelsOn hl).1
  · rw [rightExt_eq, rightExt_eq, part_levelsOn_other_succ hside hN]
    exact key _ fun l hl => (one_le_of_mem_levelsOn hl).1

/-- The chain and join extensions of a part on the other side equal the parent's. -/
theorem chainExt_part_other {σ : Context} {keep : List ℕ} {s s' : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 ≠ s') (p q : ℕ) :
    (σ.part keep s m).chainExt s' p q = σ.chainExt s' p q := by
  unfold Context.chainExt
  rw [(leftExt_part_other hside p).1, (rightExt_part_other hside q).1]

theorem joinExt_part_other {σ : Context} {keep : List ℕ} {s s' : Side} {m : ℕ}
    (hside : (σ.part keep s m).sideAt 1 ≠ s') (p q : ℕ) :
    (σ.part keep s m).joinExt s' p q = σ.joinExt s' p q := by
  unfold Context.joinExt
  rw [chainExt_part_other hside, part_levelsOn_other_zero hside, List.map_map]
  congr 3
  apply List.map_congr_left
  intro N hN
  have h1 := (one_le_of_mem_levelsOn hN).1
  simp only [Function.comp]
  rw [(leftExt_part_other hside p).2 N h1, (rightExt_part_other hside q).2 N h1, part_maximumAt_succ σ keep s m h1]


/-! ### Positions of a part -/

theorem part_childPositions (σ : Context) (keep : List ℕ) (s : Side) (m : ℕ) :
    (σ.part keep s m).childPositions = σ.childPositions.filter (· ∈ keep) := by
  unfold Context.childPositions
  rw [part_word_length, List.filter_filter]
  apply List.filter_congr
  intro p hp
  rw [List.mem_range] at hp
  rcases hσ : σ.letterAt p with _ | ⟨l₀, s₀⟩
  · rw [part_letterAt_of_child σ keep s m hp hσ]
    by_cases hmem : p ∈ keep <;> simp [hmem]
  · rw [part_letterAt_of_ext σ keep s m hp hσ]
    simp

theorem childPositions_filter_positionsOf {n : ℕ} {S T : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = S.card) (hT : T ⊆ S) :
    σ.childPositions.filter (· ∈ σ.positionsOf S T) = σ.positionsOf S T := by
  have hperm : (σ.childPositions.filter (· ∈ σ.positionsOf S T)).Perm (σ.positionsOf S T) := by
    refine (List.perm_ext_iff_of_nodup ((childPositions_nodup σ).filter _) (Finset.sort_nodup _ _)).2 ?_
    intro p
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨positionsOf_subset hlen hT p h, h⟩⟩
  exact List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (((childPositions_pairwise σ).imp le_of_lt).filter _) (Finset.pairwise_sort _ _) hperm

theorem positionsOf_pairwise_lt {n : ℕ} (σ : Context) (S T : Finset (Fin n)) :
    (σ.positionsOf S T).Pairwise (· < ·) :=
  ((Finset.pairwise_sort _ _).and (Finset.sort_nodup _ _)).imp fun h => lt_of_le_of_ne h.1 h.2

/-- In a strictly increasing list, an element sits at the index counting the smaller ones. -/
theorem getElem?_length_filter_lt {L : List ℕ} (hL : L.Pairwise (· < ·)) {x : ℕ} (hx : x ∈ L) :
    L[(L.filter (· < x)).length]? = some x := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    rcases List.mem_cons.1 hx with rfl | hx'
    · have hnil : L.filter (· < x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb
        simp only [decide_eq_true_eq, not_lt]
        exact le_of_lt (hL.1 b hb)
      simp [List.filter_cons, hnil]
    · have hax : a < x := hL.1 x hx'
      rw [List.filter_cons, if_pos (by simpa using hax)]
      simp only [List.length_cons, List.getElem?_cons_succ]
      exact ih hL.2 hx'

theorem pos_le_pos_of_le {n : ℕ} {S : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = S.card) {v w : Fin n} (hv : v ∈ S) (hw : w ∈ S) (hvw : v ≤ w) :
    (σ.childPositions[(S.filter (· < v)).card]?).getD 0 ≤
      (σ.childPositions[(S.filter (· < w)).card]?).getD 0 := by
  have h1 : (S.filter (· < v)).card < σ.childPositions.length := hlen ▸ rank_lt_card hv
  have h2 : (S.filter (· < w)).card < σ.childPositions.length := hlen ▸ rank_lt_card hw
  have hr : (S.filter (· < v)).card ≤ (S.filter (· < w)).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hvw⟩
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some]
  rcases lt_or_eq_of_le hr with hlt | heq
  · exact le_of_lt ((List.pairwise_iff_getElem.1 (childPositions_pairwise σ)) _ _ h1 h2 hlt)
  · simp only [heq, le_refl]

theorem pos_lt_pos_of_lt {n : ℕ} {S : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = S.card) {v w : Fin n} (hv : v ∈ S) (hw : w ∈ S) (hvw : v < w) :
    (σ.childPositions[(S.filter (· < v)).card]?).getD 0 <
      (σ.childPositions[(S.filter (· < w)).card]?).getD 0 := by
  have h1 : (S.filter (· < v)).card < σ.childPositions.length := hlen ▸ rank_lt_card hv
  have h2 : (S.filter (· < w)).card < σ.childPositions.length := hlen ▸ rank_lt_card hw
  rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some]
  exact (List.pairwise_iff_getElem.1 (childPositions_pairwise σ)) _ _ h1 h2 (rank_lt_rank hv hvw)

theorem lt_of_pos_lt_pos {n : ℕ} {S : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = S.card) {v w : Fin n} (hv : v ∈ S) (hw : w ∈ S)
    (h : (σ.childPositions[(S.filter (· < v)).card]?).getD 0 <
      (σ.childPositions[(S.filter (· < w)).card]?).getD 0) : v < w := by
  by_contra hle
  exact absurd h (not_lt.2 (pos_le_pos_of_le hlen hw hv (not_lt.1 hle)))

/-- The position of a vertex of a part, computed in the part, is its position in the parent. -/
theorem pos_part_eq {n : ℕ} {S T : Finset (Fin n)} {σ : Context}
    (hlen : σ.childPositions.length = S.card) (hT : T ⊆ S) (s : Side) (m : ℕ) {v : Fin n} (hv : v ∈ T) :
    ((σ.part (σ.positionsOf S T) s m).childPositions[(T.filter (· < v)).card]?).getD 0 =
      (σ.childPositions[(S.filter (· < v)).card]?).getD 0 := by
  rw [part_childPositions, childPositions_filter_positionsOf hlen hT]
  set f : Fin n → ℕ := fun w => (σ.childPositions[(S.filter (· < w)).card]?).getD 0 with hf
  have hmem : f v ∈ σ.positionsOf S T := (mem_positionsOf σ).2 ⟨v, hv, rfl⟩
  have hcount : ((σ.positionsOf S T).filter (· < f v)).length = (T.filter (· < v)).card := by
    have hperm : ((σ.positionsOf S T).filter (· < f v)).Perm
        (Finset.sort ((T.image f).filter (· < f v)) (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup ((Finset.sort_nodup _ _).filter _) (Finset.sort_nodup _ _)).2 ?_
      intro p
      simp only [List.mem_filter, decide_eq_true_eq, Finset.mem_sort, Finset.mem_filter,
        Finset.mem_image]
      exact Iff.rfl
    rw [hperm.length_eq, Finset.length_sort, Finset.filter_image,
      Finset.card_image_of_injOn ((pos_injOn hlen).mono (Finset.coe_subset.2 (Finset.filter_subset _ _ |>.trans hT)))]
    congr 1
    apply Finset.filter_congr
    intro w hw
    exact ⟨fun h => lt_of_pos_lt_pos hlen (hT hw) (hT hv) h, fun h => pos_lt_pos_of_lt hlen (hT hw) (hT hv) h⟩
  rw [← hcount, getElem?_length_filter_lt (positionsOf_pairwise_lt σ S T) hmem]
  rfl

end Context

/-! ### Chains across a deep-below split -/

/-- A cup of the lower part stays a cup after adding upper vertices that lie outside it in
sweep order, at most one on each side. -/
theorem isCupSet_union_of_extremes {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper) {C U : Finset (Fin n)} (hC : C ⊆ lower) (hcup : IsCupSet χ C)
    (hU : U ⊆ upper) (hext : ∀ u ∈ U, (∀ c ∈ C, u < c) ∨ (∀ c ∈ C, c < u))
    (hU2 : ∀ u ∈ U, ∀ u' ∈ U, u < u' → ∃ c ∈ C, u < c ∧ c < u') : IsCupSet χ (C ∪ U) := by
  intro t hi hj hk
  have hsub : C ∪ U ⊆ lower ∪ upper := Finset.union_subset_union hC hU
  have hjC : t.j ∈ C := by
    rcases Finset.mem_union.1 hj with hjC | hjU
    · exact hjC
    · exfalso
      rcases hext t.j hjU with hbelow | habove
      · -- t.i < t.j is below all of C, so t.i ∈ U, and hU2 gives c between them
        rcases Finset.mem_union.1 hi with hiC | hiU
        · exact absurd (hbelow t.i hiC) (not_lt.2 (le_of_lt t.hij))
        · obtain ⟨c, hc, h1, h2⟩ := hU2 t.i hiU t.j hjU t.hij
          exact absurd (hbelow c hc) (not_lt.2 (le_of_lt h2))
      · rcases Finset.mem_union.1 hk with hkC | hkU
        · exact absurd (habove t.k hkC) (not_lt.2 (le_of_lt t.hjk))
        · obtain ⟨c, hc, h1, h2⟩ := hU2 t.j hjU t.k hkU t.hjk
          exact absurd (habove c hc) (not_lt.2 (le_of_lt h1))
  by_cases hall : t.i ∈ C ∧ t.k ∈ C
  · exact hcup t hall.1 hjC hall.2
  · have hjl : t.j ∈ lower := hC hjC
    rw [h.crossing t (hsub hi) (hsub hj) (hsub hk) ?_ ?_, if_pos hjl]
    · intro ⟨hil, _, hkl⟩
      apply hall
      constructor
      · rcases Finset.mem_union.1 hi with hiC | hiU
        · exact hiC
        · exact absurd hil (Finset.disjoint_right.1 h.disjoint (hU hiU))
      · rcases Finset.mem_union.1 hk with hkC | hkU
        · exact hkC
        · exact absurd hkl (Finset.disjoint_right.1 h.disjoint (hU hkU))
    · intro ⟨_, hju, _⟩
      exact Finset.disjoint_left.1 h.disjoint hjl hju

/-- A cap of the upper part stays a cap after adding lower vertices outside it, at most one
on each side. -/
theorem isCapSet_union_of_extremes {n : ℕ} {χ : TripleColoring n} {lower upper : Finset (Fin n)}
    (h : HasDeepBelowSplit χ lower upper) {D L : Finset (Fin n)} (hD : D ⊆ upper) (hcap : IsCapSet χ D)
    (hL : L ⊆ lower) (hext : ∀ u ∈ L, (∀ d ∈ D, u < d) ∨ (∀ d ∈ D, d < u))
    (hL2 : ∀ u ∈ L, ∀ u' ∈ L, u < u' → ∃ d ∈ D, u < d ∧ d < u') : IsCapSet χ (D ∪ L) := by
  intro t hi hj hk
  have hsub : D ∪ L ⊆ lower ∪ upper := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact Finset.mem_union_right _ (hD hx)
    · exact Finset.mem_union_left _ (hL hx)
  have hjD : t.j ∈ D := by
    rcases Finset.mem_union.1 hj with hjD | hjL
    · exact hjD
    · exfalso
      rcases hext t.j hjL with hbelow | habove
      · rcases Finset.mem_union.1 hi with hiD | hiL
        · exact absurd (hbelow t.i hiD) (not_lt.2 (le_of_lt t.hij))
        · obtain ⟨d, hd, h1, h2⟩ := hL2 t.i hiL t.j hjL t.hij
          exact absurd (hbelow d hd) (not_lt.2 (le_of_lt h2))
      · rcases Finset.mem_union.1 hk with hkD | hkL
        · exact absurd (habove t.k hkD) (not_lt.2 (le_of_lt t.hjk))
        · obtain ⟨d, hd, h1, h2⟩ := hL2 t.j hjL t.k hkL t.hjk
          exact absurd (habove d hd) (not_lt.2 (le_of_lt h1))
  by_cases hall : t.i ∈ D ∧ t.k ∈ D
  · exact hcap t hall.1 hjD hall.2
  · have hju : t.j ∈ upper := hD hjD
    have hjl : t.j ∉ lower := Finset.disjoint_right.1 h.disjoint hju
    rw [h.crossing t (hsub hi) (hsub hj) (hsub hk) ?_ ?_, if_neg hjl]
    · intro ⟨_, hjl', _⟩
      exact hjl hjl'
    · intro ⟨hiu, _, hku⟩
      apply hall
      constructor
      · rcases Finset.mem_union.1 hi with hiD | hiL
        · exact hiD
        · exact absurd hiu (Finset.disjoint_left.1 h.disjoint (hL hiL))
      · rcases Finset.mem_union.1 hk with hkD | hkL
        · exact hkD
        · exact absurd hku (Finset.disjoint_left.1 h.disjoint (hL hkL))

/-- The longest chain is attained. -/
theorem exists_card_eq_chainMax {n : ℕ} (χ : TripleColoring n) (s : Finset (Fin n)) (b : Bool) :
    ∃ D ⊆ s, (if b then IsCupSet χ D else IsCapSet χ D) ∧ D.card = chainMax χ s b := by
  classical
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image
    (s.powerset.filter fun t => if b then IsCupSet χ t else IsCapSet χ t) Finset.card
    ⟨∅, by simp [IsCupSet, IsCapSet]⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hD
  refine ⟨D, hD.1, hD.2, le_antisymm (chainMax_le_iff.1 le_rfl D hD.1 hD.2) ?_⟩
  exact chainMax_le_iff.2 fun C hC hb =>
    hmax C (by simp only [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hC, hb⟩)

end Ctx

namespace Ctx

/-- The position of a vertex of `S` in the word of `σ`. -/
def posOf {n : ℕ} (σ : Context) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (σ.childPositions[(S.filter (· < v)).card]?).getD 0

theorem add_max_add_max_le (c d : ℕ) {La Lb : List ℕ} {a₀ b₀ : ℕ} (ha₀ : a₀ ∈ La) (hb₀ : b₀ ∈ Lb)
    (h : ∀ a ∈ La, ∀ b ∈ Lb, c + a + b ≤ d) :
    c + (La.max?).getD 0 + (Lb.max?).getD 0 ≤ d := by
  have hmb : ∀ a ∈ La, (Lb.max?).getD 0 ≤ d - (c + a) := fun a ha =>
    getD_max?_le fun b hb => Nat.le_sub_of_add_le (by have := h a ha b hb; omega)
  have hma : (La.max?).getD 0 ≤ d - c - (Lb.max?).getD 0 := by
    apply getD_max?_le
    intro a ha
    have h1 := hmb a ha
    have h2 := h a ha b₀ hb₀
    omega
  have h3 := hmb a₀ ha₀
  have h4 := h a₀ ha₀ b₀ hb₀
  omega

namespace Context

theorem chainExt_le_joinExt (σ : Context) (s : Side) (p q : ℕ) : σ.chainExt s p q ≤ σ.joinExt s p q :=
  le_max_left _ _

theorem le_joinExt_of_mem_levelsOn {σ : Context} {s : Side} {N : ℕ} (hN : N ∈ σ.levelsOn s 0) (p q : ℕ) :
    σ.leftExt s N p + σ.rightExt s N q + σ.maximumAt N ≤ σ.joinExt s p q :=
  le_max_of_le_right (le_getD_max?_of_mem (List.mem_map.2 ⟨N, hN, rfl⟩))

end Context

/-- The core of the transfer: a chain `C` of the part `T` obeys, in the part's context, the
chain and join limits on its own side, because every extension the part's context counts is
realized by a chain of the whole set `S` that the parent's context constrains. -/
theorem card_add_ext_part_le {n : ℕ} {S T T' : Finset (Fin n)} {σ : Context}
    {s : Side} {m param : ℕ} {P : Finset (Fin n) → Prop}
    (hlen : σ.childPositions.length = S.card) (hT : T ⊆ S) (hT' : T' ⊆ S) (hdisj : Disjoint T T')
    (hside : (σ.part (σ.positionsOf S T) s m).sideAt 1 = s)
    (hext1 : (σ.part (σ.positionsOf S T) s m).extPositions 1 = σ.positionsOf S T')
    (hσ : ∀ C' ⊆ S, ∀ hC' : C'.Nonempty, P C' →
      C'.card + σ.chainExt s (posOf σ S (C'.min' hC')) (posOf σ S (C'.max' hC')) ≤ param - 1 ∧
      C'.card + σ.joinExt s (posOf σ S (C'.min' hC')) (posOf σ S (C'.max' hC')) ≤ σ.k - 1)
    (hextP : ∀ C ⊆ T, P C → ∀ U ⊆ T', (∀ u ∈ U, (∀ c ∈ C, u < c) ∨ (∀ c ∈ C, c < u)) →
      (∀ u ∈ U, ∀ u' ∈ U, u < u' → ∃ c ∈ C, u < c ∧ c < u') → P (C ∪ U))
    (hjoin : ∀ C ⊆ T, P C → C.card + m ≤ σ.k - 1)
    {C : Finset (Fin n)} (hC : C ⊆ T) (hCne : C.Nonempty) (hP : P C) :
    C.card + (σ.part (σ.positionsOf S T) s m).chainExt s (posOf σ S (C.min' hCne)) (posOf σ S (C.max' hCne))
        ≤ param - 1 ∧
      C.card + (σ.part (σ.positionsOf S T) s m).joinExt s (posOf σ S (C.min' hCne)) (posOf σ S (C.max' hCne))
        ≤ σ.k - 1 := by
  classical
  set π := σ.part (σ.positionsOf S T) s m with hπ
  set p := posOf σ S (C.min' hCne) with hp
  set q := posOf σ S (C.max' hCne) with hq
  have hCS : C ⊆ S := hC.trans hT
  have hCpos : 0 < C.card := hCne.card_pos
  have hminC : C.min' hCne ∈ S := hCS (Finset.min'_mem _ _)
  have hmaxC : C.max' hCne ∈ S := hCS (Finset.max'_mem _ _)
  have hL₀ : ∀ top', ∀ l ∈ σ.levelsOn s top', 1 ≤ l := fun _ l hl => (Context.one_le_of_mem_levelsOn hl).1
  have hnotT : ∀ w ∈ T', w ∉ C := fun w hw hwC => Finset.disjoint_left.1 hdisj (hC hwC) hw
  have left_vertex : ∀ x ∈ σ.positionsOf S T', x < p → ∃ w ∈ T', posOf σ S w = x ∧ ∀ c ∈ C, w < c := by
    intro x hx hxp
    obtain ⟨w, hw, rfl⟩ := (Context.mem_positionsOf σ).1 hx
    refine ⟨w, hw, rfl, fun c hc => ?_⟩
    exact lt_of_lt_of_le (Context.lt_of_pos_lt_pos hlen (hT' hw) hminC hxp) (Finset.min'_le _ _ hc)
  have right_vertex : ∀ y ∈ σ.positionsOf S T', q < y → ∃ w ∈ T', posOf σ S w = y ∧ ∀ c ∈ C, c < w := by
    intro y hy hqy
    obtain ⟨w, hw, rfl⟩ := (Context.mem_positionsOf σ).1 hy
    refine ⟨w, hw, rfl, fun c hc => ?_⟩
    exact lt_of_le_of_lt (Finset.le_max' _ _ hc) (Context.lt_of_pos_lt_pos hlen hmaxC (hT' hw) hqy)
  -- every pair of fold values is realized by a chain of `S`
  have core : ∀ (top' a b : ℕ),
      (a ≤ σ.leftExt s top' p ∨ ∃ x ∈ σ.positionsOf S T', x < p ∧ a ≤ 1 + σ.leftExt s top' x) →
      (b ≤ σ.rightExt s top' q ∨ ∃ y ∈ σ.positionsOf S T', q < y ∧ b ≤ 1 + σ.rightExt s top' y) →
      ∃ C' ⊆ S, ∃ hC' : C'.Nonempty, P C' ∧
        C.card + a + b ≤ C'.card + σ.leftExt s top' (posOf σ S (C'.min' hC')) +
          σ.rightExt s top' (posOf σ S (C'.max' hC')) := by
    intro top' a b ha hb
    rcases ha with ha | ⟨x, hx, hxp, ha⟩ <;> rcases hb with hb | ⟨y, hy, hqy, hb⟩
    · exact ⟨C, hCS, hCne, hP, by rw [← hp, ← hq]; omega⟩
    · obtain ⟨w', hw', rfl, hw'C⟩ := right_vertex y hy hqy
      have hU : ({w'} : Finset (Fin n)) ⊆ T' := Finset.singleton_subset_iff.2 hw'
      have hP' := hextP C hC hP {w'} hU (by simpa using Or.inr hw'C)
        (by intro u hu u' hu' huu'; simp only [Finset.mem_singleton] at hu hu'; subst hu hu'; exact absurd huu' (lt_irrefl _))
      have hne : (C ∪ {w'}).Nonempty := hCne.mono Finset.subset_union_left
      have hcard : (C ∪ {w'}).card = C.card + 1 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 (hnotT w' hw')), Finset.card_singleton]
      have hmin : (C ∪ {w'}).min' hne = C.min' hCne := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_union_left _ (Finset.min'_mem _ _))
        · apply Finset.le_min'
          intro b hb
          rcases Finset.mem_union.1 hb with hb | hb
          · exact Finset.min'_le _ _ hb
          · rw [Finset.mem_singleton] at hb
            subst hb
            exact le_of_lt (hw'C _ (Finset.min'_mem _ _))
      have hmax : (C ∪ {w'}).max' hne = w' := by
        apply le_antisymm
        · apply Finset.max'_le
          intro b hb
          rcases Finset.mem_union.1 hb with hb | hb
          · exact le_of_lt (hw'C b hb)
          · rw [Finset.mem_singleton] at hb
            exact le_of_eq hb
        · exact Finset.le_max' _ _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      refine ⟨C ∪ {w'}, Finset.union_subset hCS (hU.trans hT'), hne, hP', ?_⟩
      rw [hcard, hmin, hmax, ← hp]
      omega
    · obtain ⟨w, hw, rfl, hwC⟩ := left_vertex x hx hxp
      have hU : ({w} : Finset (Fin n)) ⊆ T' := Finset.singleton_subset_iff.2 hw
      have hP' := hextP C hC hP {w} hU (by simpa using Or.inl hwC)
        (by intro u hu u' hu' huu'; simp only [Finset.mem_singleton] at hu hu'; subst hu hu'; exact absurd huu' (lt_irrefl _))
      have hne : (C ∪ {w}).Nonempty := hCne.mono Finset.subset_union_left
      have hcard : (C ∪ {w}).card = C.card + 1 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 (hnotT w hw)), Finset.card_singleton]
      have hmin : (C ∪ {w}).min' hne = w := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
        · apply Finset.le_min'
          intro b hb
          rcases Finset.mem_union.1 hb with hb | hb
          · exact le_of_lt (hwC b hb)
          · rw [Finset.mem_singleton] at hb
            exact le_of_eq hb.symm
      have hmax : (C ∪ {w}).max' hne = C.max' hCne := by
        apply le_antisymm
        · apply Finset.max'_le
          intro b hb
          rcases Finset.mem_union.1 hb with hb | hb
          · exact Finset.le_max' _ _ hb
          · rw [Finset.mem_singleton] at hb
            subst hb
            exact le_of_lt (lt_of_lt_of_le (hwC _ (Finset.min'_mem _ _)) (Finset.min'_le_max' _ _))
        · exact Finset.le_max' _ _ (Finset.mem_union_left _ (Finset.max'_mem _ _))
      refine ⟨C ∪ {w}, Finset.union_subset hCS (hU.trans hT'), hne, hP', ?_⟩
      rw [hcard, hmin, hmax, ← hq]
      omega
    · obtain ⟨w, hw, rfl, hwC⟩ := left_vertex x hx hxp
      obtain ⟨w', hw', rfl, hw'C⟩ := right_vertex y hy hqy
      have hww' : w < w' := lt_trans (hwC (C.min' hCne) (Finset.min'_mem C hCne)) (hw'C (C.min' hCne) (Finset.min'_mem C hCne))
      have hU : ({w, w'} : Finset (Fin n)) ⊆ T' := by
        intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact hw
        · rw [Finset.mem_singleton] at hu
          exact hu ▸ hw'
      have hP' := hextP C hC hP {w, w'} hU
        (by
          intro u hu
          rcases Finset.mem_insert.1 hu with rfl | hu
          · exact Or.inl hwC
          · rw [Finset.mem_singleton] at hu
            exact hu ▸ Or.inr hw'C)
        (by
          intro u hu u' hu' huu'
          have hu1 : u = w ∨ u = w' := by simpa using hu
          have hu2 : u' = w ∨ u' = w' := by simpa using hu'
          rcases hu1 with hu1 | hu1 <;> rcases hu2 with hu2 | hu2
          · rw [hu1, hu2] at huu'
            exact absurd huu' (lt_irrefl _)
          · refine ⟨C.min' hCne, Finset.min'_mem _ _, ?_, ?_⟩
            · rw [hu1]
              exact hwC _ (Finset.min'_mem _ _)
            · rw [hu2]
              exact hw'C _ (Finset.min'_mem _ _)
          · rw [hu1, hu2] at huu'
            exact absurd huu' (not_lt.2 (le_of_lt hww'))
          · rw [hu1, hu2] at huu'
            exact absurd huu' (lt_irrefl _))
      have hne : (C ∪ {w, w'}).Nonempty := hCne.mono Finset.subset_union_left
      have hdisjU : Disjoint C {w, w'} := by
        rw [Finset.disjoint_left]
        intro c hc hcU
        rcases Finset.mem_insert.1 hcU with rfl | hcU
        · exact hnotT _ hw hc
        · rw [Finset.mem_singleton] at hcU
          exact hnotT _ hw' (hcU ▸ hc)
      have hcard : (C ∪ {w, w'}).card = C.card + 2 := by
        rw [Finset.card_union_of_disjoint hdisjU, Finset.card_pair (ne_of_lt hww')]
      have hmin : (C ∪ {w, w'}).min' hne = w := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
        · apply Finset.le_min'
          intro b hb
          rcases Finset.mem_union.1 hb with hb | hb
          · exact le_of_lt (hwC b hb)
          · rcases Finset.mem_insert.1 hb with rfl | hb
            · exact le_rfl
            · rw [Finset.mem_singleton] at hb
              exact hb ▸ le_of_lt hww'
      have hmax : (C ∪ {w, w'}).max' hne = w' := by
        apply le_antisymm
        · apply Finset.max'_le
          intro b hb
          rcases Finset.mem_union.1 hb with hb | hb
          · exact le_of_lt (hw'C b hb)
          · rcases Finset.mem_insert.1 hb with rfl | hb
            · exact le_of_lt hww'
            · rw [Finset.mem_singleton] at hb
              exact le_of_eq hb
        · exact Finset.le_max' _ _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      refine ⟨C ∪ {w, w'}, Finset.union_subset hCS (hU.trans hT'), hne, hP', ?_⟩
      rw [hcard, hmin, hmax]
      omega
  -- the fold bounds of the part, rewritten through the parent
  have hfoldL : ∀ top', ∀ ls ∈ (1 :: (σ.levelsOn s top').map (· + 1)).sublists,
      (ls.foldl (Context.leftStep π) (p, 0)).2 ≤ σ.leftExt s top' p ∨
        ∃ x ∈ σ.positionsOf S T', x < p ∧ (ls.foldl (Context.leftStep π) (p, 0)).2 ≤ 1 + σ.leftExt s top' x := by
    intro top' ls hls
    rcases Context.foldl_leftStep_part_le (hL₀ top') p hls with h | ⟨x, hx, hxp, h⟩
    · exact Or.inl (by rw [Context.leftExt_eq]; exact h)
    · exact Or.inr ⟨x, hext1 ▸ hx, hxp, by rw [Context.leftExt_eq]; exact h⟩
  have hfoldR : ∀ top', ∀ ls ∈ (1 :: (σ.levelsOn s top').map (· + 1)).sublists,
      (ls.foldl (Context.rightStep π) (q, 0)).2 ≤ σ.rightExt s top' q ∨
        ∃ y ∈ σ.positionsOf S T', q < y ∧ (ls.foldl (Context.rightStep π) (q, 0)).2 ≤ 1 + σ.rightExt s top' y := by
    intro top' ls hls
    rcases Context.foldl_rightStep_part_le (hL₀ top') q hls with h | ⟨y, hy, hqy, h⟩
    · exact Or.inl (by rw [Context.rightExt_eq]; exact h)
    · exact Or.inr ⟨y, hext1 ▸ hy, hqy, by rw [Context.rightExt_eq]; exact h⟩
  have hnil : ∀ L : List ℕ, ([] : List ℕ) ∈ L.sublists := fun L => List.mem_sublists.2 (List.nil_sublist L)
  -- the chain extension of the part at level `top` (0 or a shifted parent level)
  have chain_bound : ∀ (top' : ℕ) (LL : List ℕ), LL = 1 :: (σ.levelsOn s top').map (· + 1) →
      ∀ d, (∀ C' ⊆ S, ∀ hC' : C'.Nonempty, P C' →
        C'.card + σ.leftExt s top' (posOf σ S (C'.min' hC')) + σ.rightExt s top' (posOf σ S (C'.max' hC')) ≤ d) →
      C.card + ((LL.sublists.map fun ls => (ls.foldl (Context.leftStep π) (p, 0)).2).max?).getD 0 +
        ((LL.sublists.map fun ls => (ls.foldl (Context.rightStep π) (q, 0)).2).max?).getD 0 ≤ d := by
    intro top' LL hLL d hd
    apply add_max_add_max_le C.card d (List.mem_map.2 ⟨[], hnil _, rfl⟩) (List.mem_map.2 ⟨[], hnil _, rfl⟩)
    intro a ha b hb
    obtain ⟨lsL, hlsL, rfl⟩ := List.mem_map.1 ha
    obtain ⟨lsR, hlsR, rfl⟩ := List.mem_map.1 hb
    rw [hLL] at hlsL hlsR
    obtain ⟨C', hC'S, hC'ne, hP', hle⟩ := core top' _ _ (hfoldL top' lsL hlsL) (hfoldR top' lsR hlsR)
    have := hd C' hC'S hC'ne hP'
    omega
  constructor
  · -- chain extension against `param - 1`
    have := chain_bound 0 (π.levelsOn s 0) (Context.part_levelsOn_self_zero hside) (param - 1)
      fun C' hC'S hC'ne hP' => by
        have h := (hσ C' hC'S hC'ne hP').1
        unfold Context.chainExt at h
        omega
    unfold Context.chainExt
    rw [Context.leftExt_eq, Context.rightExt_eq]
    omega
  · -- join extension against `k - 1`
    have hchain : C.card + π.chainExt s p q ≤ σ.k - 1 := by
      have := chain_bound 0 (π.levelsOn s 0) (Context.part_levelsOn_self_zero hside) (σ.k - 1)
        fun C' hC'S hC'ne hP' => by
          have h1 := (hσ C' hC'S hC'ne hP').2
          have h2 := Context.chainExt_le_joinExt σ s (posOf σ S (C'.min' hC'ne)) (posOf σ S (C'.max' hC'ne))
          unfold Context.chainExt at h2
          omega
      unfold Context.chainExt
      rw [Context.leftExt_eq, Context.rightExt_eq]
      omega
    have hk1 : C.card ≤ σ.k - 1 := by have := hjoin C hC hP; omega
    have hM : C.card + (((1 :: (σ.levelsOn s 0).map (· + 1)).map fun N =>
        π.leftExt s N p + π.rightExt s N q + π.maximumAt N).max?).getD 0 ≤ σ.k - 1 := by
      have hterms : ∀ t ∈ ((1 :: (σ.levelsOn s 0).map (· + 1)).map fun N =>
          π.leftExt s N p + π.rightExt s N q + π.maximumAt N), C.card + t ≤ σ.k - 1 := by
        intro t ht
        obtain ⟨N, hN, rfl⟩ := List.mem_map.1 ht
        rcases List.mem_cons.1 hN with rfl | hN
        · rw [Context.leftExt_one, Context.rightExt_one, Context.part_maximumAt_one]
          simpa using hjoin C hC hP
        · obtain ⟨N', hN', rfl⟩ := List.mem_map.1 hN
          have h1 := (Context.one_le_of_mem_levelsOn hN').1
          rw [Context.part_maximumAt_succ σ _ s m h1, Context.leftExt_eq, Context.rightExt_eq,
            Context.part_levelsOn_self_succ hside h1]
          have := chain_bound N' _ rfl (σ.k - 1 - σ.maximumAt N') fun C' hC'S hC'ne hP' => by
            have hj := (hσ C' hC'S hC'ne hP').2
            have hm := Context.le_joinExt_of_mem_levelsOn hN' (posOf σ S (C'.min' hC'ne)) (posOf σ S (C'.max' hC'ne))
            omega
          omega
      have := getD_max?_le (L := (1 :: (σ.levelsOn s 0).map (· + 1)).map fun N =>
          π.leftExt s N p + π.rightExt s N q + π.maximumAt N)
        (b := σ.k - 1 - C.card) fun t ht => Nat.le_sub_of_add_le (by have := hterms t ht; omega)
      omega
    unfold Context.joinExt
    rw [Context.part_levelsOn_self_zero hside]
    omega

end Ctx

/-- Context transfer (experiment 0117, the union lemma): across a deep-below split of a child satisfying σ, the lower part satisfies σ with the upper part added as a level-1 sibling of longest cap capmax(upper), and the upper part satisfies σ with the lower part added as a level-1 sibling of longest cup cupmax(lower). Proved from the four-vertex law: mixed quadruples, chains extend by one vertex per side per level, strong sets join at one level. Verified on all 1,367,052 subtrees at n <= 8.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_card_le_bound -/
theorem ctx_satisfies_of_deepBelowSplit {n : ℕ} {χ : TripleColoring n} {S lower upper : Finset (Fin n)} (σ : Ctx.Context) (hwf : σ.WellFormed) (hS : Ctx.Satisfies χ S σ) (hsplit : HasDeepBelowSplit χ lower upper) (hunion : lower ∪ upper = S) (hl : lower.Nonempty) (hu : upper.Nonempty) : Ctx.Satisfies χ lower (σ.part (σ.positionsOf S lower) Ctx.Side.lower (Ctx.chainMax χ upper false)) ∧ Ctx.Satisfies χ upper (σ.part (σ.positionsOf S upper) Ctx.Side.upper (Ctx.chainMax χ lower true)) := by
  subst hunion
  classical
  have hlet1 : ∀ p l s', σ.letterAt p = Ctx.Letter.ext l s' → 1 ≤ l :=
    fun p l s' h => (hwf.2.2.2.2.2 p l s' h).1
  have hlen : σ.childPositions.length = (lower ∪ upper).card := hS.1
  have hdisj := hsplit.disjoint
  have hcomplL : σ.childPositions.filter (fun p => p ∉ σ.positionsOf (lower ∪ upper) lower) =
      σ.positionsOf (lower ∪ upper) upper := Ctx.positionsOf_compl hlen hdisj
  have hcomplU : σ.childPositions.filter (fun p => p ∉ σ.positionsOf (lower ∪ upper) upper) =
      σ.positionsOf (lower ∪ upper) lower := by
    have := Ctx.positionsOf_compl (lower := upper) (upper := lower) (by rwa [Finset.union_comm]) hdisj.symm
    rwa [Finset.union_comm] at this
  -- the parent's constraints in additive form
  have hσcup : ∀ C' ⊆ lower ∪ upper, ∀ hC' : C'.Nonempty, IsCupSet χ C' →
      C'.card + σ.chainExt Ctx.Side.lower (Ctx.posOf σ (lower ∪ upper) (C'.min' hC'))
          (Ctx.posOf σ (lower ∪ upper) (C'.max' hC')) ≤ σ.u - 1 ∧
      C'.card + σ.joinExt Ctx.Side.lower (Ctx.posOf σ (lower ∪ upper) (C'.min' hC'))
          (Ctx.posOf σ (lower ∪ upper) (C'.max' hC')) ≤ σ.k - 1 := by
    intro C' hC' hne hcup
    have h := (hS.2 C' hC' hne).1 hcup
    have hpos := hne.card_pos
    change C'.card ≤ min (σ.u - 1 - σ.chainExt Ctx.Side.lower (Ctx.posOf σ (lower ∪ upper) (C'.min' hne))
      (Ctx.posOf σ (lower ∪ upper) (C'.max' hne))) (σ.k - 1 - σ.joinExt Ctx.Side.lower
      (Ctx.posOf σ (lower ∪ upper) (C'.min' hne)) (Ctx.posOf σ (lower ∪ upper) (C'.max' hne))) at h
    have h1 := h.trans (min_le_left _ _)
    have h2 := h.trans (min_le_right _ _)
    constructor <;> omega
  have hσcap : ∀ C' ⊆ lower ∪ upper, ∀ hC' : C'.Nonempty, IsCapSet χ C' →
      C'.card + σ.chainExt Ctx.Side.upper (Ctx.posOf σ (lower ∪ upper) (C'.min' hC'))
          (Ctx.posOf σ (lower ∪ upper) (C'.max' hC')) ≤ σ.a - 1 ∧
      C'.card + σ.joinExt Ctx.Side.upper (Ctx.posOf σ (lower ∪ upper) (C'.min' hC'))
          (Ctx.posOf σ (lower ∪ upper) (C'.max' hC')) ≤ σ.k - 1 := by
    intro C' hC' hne hcap
    have h := (hS.2 C' hC' hne).2.1 hcap
    have hpos := hne.card_pos
    change C'.card ≤ min (σ.a - 1 - σ.chainExt Ctx.Side.upper (Ctx.posOf σ (lower ∪ upper) (C'.min' hne))
      (Ctx.posOf σ (lower ∪ upper) (C'.max' hne))) (σ.k - 1 - σ.joinExt Ctx.Side.upper
      (Ctx.posOf σ (lower ∪ upper) (C'.min' hne)) (Ctx.posOf σ (lower ∪ upper) (C'.max' hne))) at h
    have h1 := h.trans (min_le_left _ _)
    have h2 := h.trans (min_le_right _ _)
    constructor <;> omega
  -- joins with the sibling's longest chain
  have hjoinL : ∀ C ⊆ lower, IsCupSet χ C → C.card + Ctx.chainMax χ upper false ≤ σ.k - 1 := by
    intro C hC hcup
    obtain ⟨D, hD, hDcap, hDcard⟩ := Ctx.exists_card_eq_chainMax χ upper false
    simp only [Bool.false_eq_true, if_false] at hDcap
    have hstrong := hsplit.cup_union_cap_isStrongPolygonSet hC hD hcup hDcap
    rcases (C ∪ D).eq_empty_or_nonempty with hemp | hne
    · rw [Finset.union_eq_empty] at hemp
      rw [← hDcard, hemp.1, hemp.2]
      simp
    · have := (hS.2 (C ∪ D) (Finset.union_subset_union hC hD) hne).2.2 hstrong
      rw [Finset.card_union_of_disjoint (hdisj.mono hC hD), hDcard] at this
      exact this
  have hjoinU : ∀ C ⊆ upper, IsCapSet χ C → C.card + Ctx.chainMax χ lower true ≤ σ.k - 1 := by
    intro C hC hcap
    obtain ⟨D, hD, hDcup, hDcard⟩ := Ctx.exists_card_eq_chainMax χ lower true
    simp only [if_true] at hDcup
    have hstrong := hsplit.cup_union_cap_isStrongPolygonSet hD hC hDcup hcap
    rcases (D ∪ C).eq_empty_or_nonempty with hemp | hne
    · rw [Finset.union_eq_empty] at hemp
      rw [← hDcard, hemp.1, hemp.2]
      simp
    · have := (hS.2 (D ∪ C) (Finset.union_subset_union hD hC) hne).2.2 hstrong
      rw [Finset.card_union_of_disjoint (hdisj.mono hD hC), hDcard, Nat.add_comm] at this
      exact this
  -- sides and level-one letters of the parts
  have hsideL : (σ.part (σ.positionsOf (lower ∪ upper) lower) Ctx.Side.lower (Ctx.chainMax χ upper false)).sideAt 1 =
      Ctx.Side.lower := Ctx.Context.part_sideAt_one_lower hlet1 _ _
  have hext1L : (σ.part (σ.positionsOf (lower ∪ upper) lower) Ctx.Side.lower (Ctx.chainMax χ upper false)).extPositions 1 =
      σ.positionsOf (lower ∪ upper) upper := by
    rw [Ctx.Context.part_extPositions_one hlet1]
    exact hcomplL
  have hext1U : (σ.part (σ.positionsOf (lower ∪ upper) upper) Ctx.Side.upper (Ctx.chainMax χ lower true)).extPositions 1 =
      σ.positionsOf (lower ∪ upper) lower := by
    rw [Ctx.Context.part_extPositions_one hlet1]
    exact hcomplU
  have hsideU : (σ.part (σ.positionsOf (lower ∪ upper) upper) Ctx.Side.upper (Ctx.chainMax χ lower true)).sideAt 1 =
      Ctx.Side.upper := by
    obtain ⟨q, hq⟩ : ∃ q, q ∈ (σ.part (σ.positionsOf (lower ∪ upper) upper) Ctx.Side.upper
        (Ctx.chainMax χ lower true)).extPositions 1 := by
      rw [hext1U]
      rcases hpl : σ.positionsOf (lower ∪ upper) lower with _ | ⟨q, rest⟩
      · exact absurd hpl (Ctx.positionsOf_ne_nil σ hl)
      · exact ⟨q, List.mem_cons_self ..⟩
    exact Ctx.Context.part_sideAt_one_of_mem hlet1 _ _ _ hq
  constructor
  · refine ⟨?_, ?_⟩
    · rw [Ctx.Context.part_childPositions,
        Ctx.Context.childPositions_filter_positionsOf hlen Finset.subset_union_left,
        Ctx.Context.positionsOf, Finset.length_sort,
        Finset.card_image_of_injOn ((Ctx.Context.pos_injOn hlen).mono (Finset.coe_subset.2 Finset.subset_union_left))]
    · intro C hC hCne
      have hpmin := Ctx.Context.pos_part_eq hlen Finset.subset_union_left Ctx.Side.lower
        (Ctx.chainMax χ upper false) (hC (Finset.min'_mem C hCne))
      have hpmax := Ctx.Context.pos_part_eq hlen Finset.subset_union_left Ctx.Side.lower
        (Ctx.chainMax χ upper false) (hC (Finset.max'_mem C hCne))
      dsimp only
      rw [hpmin, hpmax]
      refine ⟨fun hcup => ?_, fun hcap => ?_,
        fun hstrong => (hS.2 C (hC.trans Finset.subset_union_left) hCne).2.2 hstrong⟩
      · obtain ⟨h1, h2⟩ := Ctx.card_add_ext_part_le (S := lower ∪ upper) (T := lower) (T' := upper)
          (s := Ctx.Side.lower) (m := Ctx.chainMax χ upper false) (param := σ.u) (P := IsCupSet χ)
          hlen Finset.subset_union_left Finset.subset_union_right hdisj hsideL hext1L hσcup
          (fun C hC hcup U hU h1 h2 => Ctx.isCupSet_union_of_extremes hsplit hC hcup hU h1 h2)
          hjoinL hC hCne hcup
        exact le_min (Nat.le_sub_of_add_le h1) (Nat.le_sub_of_add_le h2)
      · have hne : (σ.part (σ.positionsOf (lower ∪ upper) lower) Ctx.Side.lower
            (Ctx.chainMax χ upper false)).sideAt 1 ≠ Ctx.Side.upper := by rw [hsideL]; decide
        show C.card ≤ min _ _
        rw [Ctx.Context.chainExt_part_other hne, Ctx.Context.joinExt_part_other hne]
        exact (hS.2 C (hC.trans Finset.subset_union_left) hCne).2.1 hcap
  · refine ⟨?_, ?_⟩
    · rw [Ctx.Context.part_childPositions,
        Ctx.Context.childPositions_filter_positionsOf hlen Finset.subset_union_right,
        Ctx.Context.positionsOf, Finset.length_sort,
        Finset.card_image_of_injOn ((Ctx.Context.pos_injOn hlen).mono (Finset.coe_subset.2 Finset.subset_union_right))]
    · intro C hC hCne
      have hpmin := Ctx.Context.pos_part_eq hlen Finset.subset_union_right Ctx.Side.upper
        (Ctx.chainMax χ lower true) (hC (Finset.min'_mem C hCne))
      have hpmax := Ctx.Context.pos_part_eq hlen Finset.subset_union_right Ctx.Side.upper
        (Ctx.chainMax χ lower true) (hC (Finset.max'_mem C hCne))
      dsimp only
      rw [hpmin, hpmax]
      refine ⟨fun hcup => ?_, fun hcap => ?_,
        fun hstrong => (hS.2 C (hC.trans Finset.subset_union_right) hCne).2.2 hstrong⟩
      · have hne : (σ.part (σ.positionsOf (lower ∪ upper) upper) Ctx.Side.upper
            (Ctx.chainMax χ lower true)).sideAt 1 ≠ Ctx.Side.lower := by rw [hsideU]; decide
        show C.card ≤ min _ _
        rw [Ctx.Context.chainExt_part_other hne, Ctx.Context.joinExt_part_other hne]
        exact (hS.2 C (hC.trans Finset.subset_union_right) hCne).1 hcup
      · obtain ⟨h1, h2⟩ := Ctx.card_add_ext_part_le (S := lower ∪ upper) (T := upper) (T' := lower)
          (s := Ctx.Side.upper) (m := Ctx.chainMax χ lower true) (param := σ.a) (P := IsCapSet χ)
          hlen Finset.subset_union_right Finset.subset_union_left hdisj.symm hsideU hext1U hσcap
          (fun C hC hcap U hU h1 h2 => Ctx.isCapSet_union_of_extremes hsplit hC hcap hU h1 h2)
          hjoinU hC hCne hcap
        exact le_min (Nat.le_sub_of_add_le h1) (Nat.le_sub_of_add_le h2)


end ErdosSzekeres
