import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Exact capacity normalization for every descendant prefix inside a single ancestor child run. Absorb all older external levels into the ancestor cup/cap parameters and truncate the active maxima domain to the new prefix, preserving both limits at every pair of ancestor child positions. The normalized raw context retains coordinates; no well-formedness claim is made for its ignored old labels. Supports a recursive-bound normalization before the unbounded outer-block comparison.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_single_run_descendant_limits_normalize (σ : Ctx.Context) (b N : ℕ)
  (hpos : σ.childPositions = List.range' b N)
  (π : Ctx.Context) (D : ℕ)
  (hπ : π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧
    π.maxima.length = D + σ.maxima.length ∧
    (∀ l, 1 ≤ l → π.extPositions (l + D) = σ.extPositions l) ∧
    (∀ l, 1 ≤ l → π.sideAt (l + D) = σ.sideAt l) ∧
    (∀ l, 1 ≤ l → π.maximumAt (l + D) = σ.maximumAt l))
  (hnew : ∀ l x, 1 ≤ l → l ≤ D → x ∈ π.extPositions l → x ∈ σ.childPositions)
  (p q : ℕ) (hp : p ∈ σ.childPositions) (hq : q ∈ σ.childPositions) :
  let τ : Ctx.Context := { π with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := π.maxima.take D }
  π.cupLimit p q = τ.cupLimit p q ∧ π.capLimit p q = τ.capLimit p q := by
  classical
  dsimp only
  let τ : Context := { π with a := σ.capLimit b b + 1, u := σ.cupLimit b b + 1, maxima := π.maxima.take D }
  change π.cupLimit p q = τ.cupLimit p q ∧ π.capLimit p q = τ.capLimit p q
  obtain ⟨ha, hu, hk, hlen, hext, hside, hmaximum⟩ := hπ
  let rootLength := N
  have hchild : ∀ p, p ∈ σ.childPositions ↔ b ≤ p ∧ p < b + rootLength := by
    intro p
    rw [hpos, List.mem_range'_1]
  -- Every old external position lies outside the run. Moving the starting child
  -- within the run therefore leaves both extension folds unchanged.
  have hextOutside : ∀ N p, p ∈ σ.extPositions N → p < b ∨ b + rootLength ≤ p := by
    intro N p hp
    by_contra hout
    have hc := (hchild p).2 ⟨by omega, by omega⟩
    have hlet : σ.letterAt p = Letter.child := of_decide_eq_true (List.mem_filter.1 hc).2
    simp [extPositions, hlet] at hp
  have hfilters : ∀ p q, p ∈ σ.childPositions → q ∈ σ.childPositions → ∀ N,
      (σ.extPositions N).filter (· < p) = (σ.extPositions N).filter (· < q) ∧
      (σ.extPositions N).filter (p < ·) = (σ.extPositions N).filter (q < ·) := by
    intro p q hp hq N
    have hp' := (hchild p).1 hp
    have hq' := (hchild q).1 hq
    constructor <;> apply List.filter_congr <;> intro x hx
    · have := hextOutside N x hx
      simp only [decide_eq_decide]
      omega
    · have := hextOutside N x hx
      simp only [decide_eq_decide]
      omega
  have hfoldLeft : ∀ (ls : List ℕ) p q c, p ∈ σ.childPositions → q ∈ σ.childPositions →
      (ls.foldl (leftStep σ) (p, c)).2 = (ls.foldl (leftStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p q c hp hq
      simp only [List.foldl_cons, leftStep]
      rw [(hfilters p q hp hq N).1]
      split
      · rfl
      · exact ih p q c hp hq
  have hfoldRight : ∀ (ls : List ℕ) p q c, p ∈ σ.childPositions → q ∈ σ.childPositions →
      (ls.foldl (rightStep σ) (p, c)).2 = (ls.foldl (rightStep σ) (q, c)).2 := by
    intro ls
    induction ls with
    | nil => intros; rfl
    | cons N ls ih =>
      intro p q c hp hq
      simp only [List.foldl_cons, rightStep]
      rw [(hfilters p q hp hq N).2]
      split
      · rfl
      · exact ih p q c hp hq
  have hleftEq : ∀ s top p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.leftExt s top p = σ.leftExt s top q := by
    intro s top p q hp hq
    simp only [leftExt_eq]
    congr 2
    apply List.map_congr_left
    intro ls _
    exact hfoldLeft ls p q 0 hp hq
  have hrightEq : ∀ s top p q, p ∈ σ.childPositions → q ∈ σ.childPositions →
      σ.rightExt s top p = σ.rightExt s top q := by
    intro s top p q hp hq
    simp only [rightExt_eq]
    congr 2
    apply List.map_congr_left
    intro ls _
    exact hfoldRight ls p q 0 hp hq
  have hmaxWitness : ∀ (L : List ℕ) (f : List ℕ → ℕ),
      ∃ ls ∈ L.sublists, ((L.sublists.map f).max?).getD 0 = f ls := by
    intro L f
    have hmem : f [] ∈ L.sublists.map f := List.mem_map.2 ⟨[], by simp, rfl⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (List.isSome_max?_of_mem hmem)
    obtain ⟨ls, hls, hval⟩ := List.mem_map.1 (List.max?_mem hv)
    exact ⟨ls, hls, by simp [hv, hval]⟩
  have hb : b ∈ σ.childPositions := by
    have hp' := (hchild p).1 hp
    apply (hchild b).2
    omega
  have hτlen : τ.maxima.length = D := by
    simp only [τ, List.length_take, hlen]
    omega
  have hτext : ∀ l, τ.extPositions l = π.extPositions l := fun _ => rfl
  have hτside : ∀ l, τ.sideAt l = π.sideAt l := fun _ => rfl
  have hτleftStep : leftStep τ = leftStep π := rfl
  have hτrightStep : rightStep τ = rightStep π := rfl
  have hτmaximum : ∀ l, 1 ≤ l → l ≤ D → τ.maximumAt l = π.maximumAt l := by
    intro l hl hD
    simp only [maximumAt, τ, List.getElem?_take_of_lt (by omega : l - 1 < D)]
  have hτprefix (s : Side) : τ.levelsOn s 0 =
      ((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s) := by
    simp [levelsOn, levels, hτlen, hτside]
  have hτmem : ∀ s top l, l ∈ τ.levelsOn s top → 1 ≤ l ∧ l ≤ D := by
    intro s top l hl
    obtain ⟨hm, _⟩ := List.mem_filter.mp hl
    change l ∈ (List.range τ.maxima.length).map (· + 1) at hm
    rw [hτlen] at hm
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    have := List.mem_range.mp hi
    omega
  have hnewFoldLeft : ∀ (ls : List ℕ), (∀ l ∈ ls, 1 ≤ l ∧ l ≤ D) →
      ∀ z c, z ∈ σ.childPositions → (ls.foldl (leftStep π) (z, c)).1 ∈ σ.childPositions := by
    intro ls
    induction ls with
    | nil => intro _ z c hz; exact hz
    | cons l ls ih =>
      intro hls z c hz
      have hl := hls l (by simp)
      have htail : ∀ n ∈ ls, 1 ≤ n ∧ n ≤ D := fun n hn => hls n (by simp [hn])
      simp only [List.foldl_cons, leftStep]
      cases hh : ((π.extPositions l).filter (· < z)).getLast? with
      | none => exact ih htail z c hz
      | some x =>
        have hx := (List.mem_filter.mp (List.mem_of_mem_getLast? (Option.mem_def.mpr hh))).1
        exact ih htail x (c + 1) (hnew l x hl.1 hl.2 hx)
  have hnewFoldRight : ∀ (ls : List ℕ), (∀ l ∈ ls, 1 ≤ l ∧ l ≤ D) →
      ∀ z c, z ∈ σ.childPositions → (ls.foldl (rightStep π) (z, c)).1 ∈ σ.childPositions := by
    intro ls
    induction ls with
    | nil => intro _ z c hz; exact hz
    | cons l ls ih =>
      intro hls z c hz
      have hl := hls l (by simp)
      have htail : ∀ n ∈ ls, 1 ≤ n ∧ n ≤ D := fun n hn => hls n (by simp [hn])
      simp only [List.foldl_cons, rightStep]
      cases hh : ((π.extPositions l).filter (z < ·)).head? with
      | none => exact ih htail z c hz
      | some x =>
        have hx := (List.mem_filter.mp (List.mem_of_mem_head? (Option.mem_def.mpr hh))).1
        exact ih htail x (c + 1) (hnew l x hl.1 hl.2 hx)
  have hlevelPrefix (π : Context) (D : ℕ) (hlen : π.maxima.length = D + σ.maxima.length)
      (hside : ∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N) (s : Side) (N : ℕ) :
      π.levelsOn s (if N = 0 then 0 else N + D) =
        ((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s) ++
          (σ.levelsOn s N).map (· + D) := by
    have hlevels : π.levels = (List.range D).map (· + 1) ++ σ.levels.map (· + D) := by
      simp only [levels, hlen, List.range_add, List.map_append, List.map_map]
      congr 2
      funext i
      simp only [Function.comp_def]
      omega
    unfold levelsOn
    rw [hlevels, List.filter_append]
    congr 1
    · apply List.filter_congr
      intro l hl
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      have hi' := List.mem_range.mp hi
      by_cases hN : N = 0
      · simp [hN]
      · simp [hN]
        omega
    · rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro l hl
      have hl1 := one_le_of_mem_levels hl
      simp only [Function.comp_def, hside l hl1, decide_eq_decide]
      by_cases hN : N = 0 <;> simp [hN]
  have hfoldOldLeft (π : Context) (D : ℕ)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
      ((ls.map (· + D)).foldl (leftStep π) st) = ls.foldl (leftStep σ) st := by
    induction ls generalizing st with
    | nil => rfl
    | cons N ls ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep : leftStep π st (N + D) = leftStep σ st N := by
        rcases st with ⟨p, c⟩
        simp only [leftStep, hext N (hls N (by simp))]
      rw [hstep]
      exact ih (fun N hN => hls N (by simp [hN])) _
  have hfoldOldRight (π : Context) (D : ℕ)
      (hext : ∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N)
      (ls : List ℕ) (hls : ∀ N ∈ ls, 1 ≤ N) (st : ℕ × ℕ) :
      ((ls.map (· + D)).foldl (rightStep π) st) = ls.foldl (rightStep σ) st := by
    induction ls generalizing st with
    | nil => rfl
    | cons N ls ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hstep : rightStep π st (N + D) = rightStep σ st N := by
        rcases st with ⟨p, c⟩
        simp only [rightStep, hext N (hls N (by simp))]
      rw [hstep]
      exact ih (fun N hN => hls N (by simp [hN])) _
  have hsplitLevels (s : Side) (top : ℕ) :
      π.levelsOn s (if top = 0 then 0 else top + D) =
        τ.levelsOn s 0 ++ (σ.levelsOn s top).map (· + D) := by
    rw [hlevelPrefix π D hlen hside, hτprefix]
  have hleftExact (s : Side) (top z : ℕ) (hz : z ∈ σ.childPositions) :
      π.leftExt s (if top = 0 then 0 else top + D) z =
        τ.leftExt s 0 z + σ.leftExt s top b := by
    have hsum (A B : List ℕ) (hA : A.Sublist (τ.levelsOn s 0))
        (hB : B.Sublist (σ.levelsOn s top)) :
        ((A ++ B.map (· + D)).foldl (leftStep π) (z, 0)).2 =
          (A.foldl (leftStep τ) (z, 0)).2 + (B.foldl (leftStep σ) (b, 0)).2 := by
      have hr := hnewFoldLeft A (fun l hl => hτmem s 0 l (hA.subset hl)) z 0 hz
      rw [List.foldl_append, hfoldOldLeft π D hext B
        (fun l hl => (one_le_of_mem_levelsOn (hB.subset hl)).1)]
      let st := A.foldl (leftStep π) (z, 0)
      change (B.foldl (leftStep σ) (st.1, st.2)).2 = st.2 + (B.foldl (leftStep σ) (b, 0)).2
      rw [foldl_leftStep_count, hfoldLeft B st.1 b 0 hr hb]
    apply le_antisymm
    · rw [leftExt_eq]
      apply getD_max?_le
      intro v hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      have hsub := List.mem_sublists.mp hls
      rw [hsplitLevels] at hsub
      obtain ⟨A, B', rfl, hA, hB'⟩ := List.sublist_append_iff.mp hsub
      obtain ⟨B, hB, rfl⟩ := List.sublist_map_iff.mp hB'
      rw [hsum A B hA hB]
      exact Nat.add_le_add
        (le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (leftStep τ) (z, 0)).2))
          (List.mem_map.mpr ⟨A, List.mem_sublists.mpr hA, rfl⟩))
        (le_getD_max?_of_mem (L := (σ.levelsOn s top).sublists.map
          (fun ls => (ls.foldl (leftStep σ) (b, 0)).2))
          (List.mem_map.mpr ⟨B, List.mem_sublists.mpr hB, rfl⟩))
    · obtain ⟨A, hA, hAval⟩ := hmaxWitness (τ.levelsOn s 0)
        (fun ls => (ls.foldl (leftStep τ) (z, 0)).2)
      obtain ⟨B, hB, hBval⟩ := hmaxWitness (σ.levelsOn s top)
        (fun ls => (ls.foldl (leftStep σ) (b, 0)).2)
      have hsub : (A ++ B.map (· + D)).Sublist
          (π.levelsOn s (if top = 0 then 0 else top + D)) := by
        rw [hsplitLevels]
        exact (List.mem_sublists.mp hA).append ((List.mem_sublists.mp hB).map _)
      have hv := le_getD_max?_of_mem (L :=
        (π.levelsOn s (if top = 0 then 0 else top + D)).sublists.map
          (fun ls => (ls.foldl (leftStep π) (z, 0)).2))
          (List.mem_map.mpr ⟨A ++ B.map (· + D), List.mem_sublists.mpr hsub, rfl⟩)
      rw [hsum A B (List.mem_sublists.mp hA) (List.mem_sublists.mp hB)] at hv
      change τ.leftExt s 0 z + σ.leftExt s top b ≤ π.leftExt s (if top = 0 then 0 else top + D) z
      rw [leftExt_eq τ, leftExt_eq σ, hAval, hBval]
      exact hv
  have hrightExact (s : Side) (top z : ℕ) (hz : z ∈ σ.childPositions) :
      π.rightExt s (if top = 0 then 0 else top + D) z =
        τ.rightExt s 0 z + σ.rightExt s top b := by
    have hsum (A B : List ℕ) (hA : A.Sublist (τ.levelsOn s 0))
        (hB : B.Sublist (σ.levelsOn s top)) :
        ((A ++ B.map (· + D)).foldl (rightStep π) (z, 0)).2 =
          (A.foldl (rightStep τ) (z, 0)).2 + (B.foldl (rightStep σ) (b, 0)).2 := by
      have hr := hnewFoldRight A (fun l hl => hτmem s 0 l (hA.subset hl)) z 0 hz
      rw [List.foldl_append, hfoldOldRight π D hext B
        (fun l hl => (one_le_of_mem_levelsOn (hB.subset hl)).1)]
      let st := A.foldl (rightStep π) (z, 0)
      change (B.foldl (rightStep σ) (st.1, st.2)).2 = st.2 + (B.foldl (rightStep σ) (b, 0)).2
      rw [foldl_rightStep_count, hfoldRight B st.1 b 0 hr hb]
    apply le_antisymm
    · rw [rightExt_eq]
      apply getD_max?_le
      intro v hv
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hv
      have hsub := List.mem_sublists.mp hls
      rw [hsplitLevels] at hsub
      obtain ⟨A, B', rfl, hA, hB'⟩ := List.sublist_append_iff.mp hsub
      obtain ⟨B, hB, rfl⟩ := List.sublist_map_iff.mp hB'
      rw [hsum A B hA hB]
      exact Nat.add_le_add
        (le_getD_max?_of_mem (L := (τ.levelsOn s 0).sublists.map
          (fun ls => (ls.foldl (rightStep τ) (z, 0)).2))
          (List.mem_map.mpr ⟨A, List.mem_sublists.mpr hA, rfl⟩))
        (le_getD_max?_of_mem (L := (σ.levelsOn s top).sublists.map
          (fun ls => (ls.foldl (rightStep σ) (b, 0)).2))
          (List.mem_map.mpr ⟨B, List.mem_sublists.mpr hB, rfl⟩))
    · obtain ⟨A, hA, hAval⟩ := hmaxWitness (τ.levelsOn s 0)
        (fun ls => (ls.foldl (rightStep τ) (z, 0)).2)
      obtain ⟨B, hB, hBval⟩ := hmaxWitness (σ.levelsOn s top)
        (fun ls => (ls.foldl (rightStep σ) (b, 0)).2)
      have hsub : (A ++ B.map (· + D)).Sublist
          (π.levelsOn s (if top = 0 then 0 else top + D)) := by
        rw [hsplitLevels]
        exact (List.mem_sublists.mp hA).append ((List.mem_sublists.mp hB).map _)
      have hv := le_getD_max?_of_mem (L :=
        (π.levelsOn s (if top = 0 then 0 else top + D)).sublists.map
          (fun ls => (ls.foldl (rightStep π) (z, 0)).2))
          (List.mem_map.mpr ⟨A ++ B.map (· + D), List.mem_sublists.mpr hsub, rfl⟩)
      rw [hsum A B (List.mem_sublists.mp hA) (List.mem_sublists.mp hB)] at hv
      change τ.rightExt s 0 z + σ.rightExt s top b ≤ π.rightExt s (if top = 0 then 0 else top + D) z
      rw [rightExt_eq τ, rightExt_eq σ, hAval, hBval]
      exact hv
  have hlevels : π.levels = τ.levels ++ σ.levels.map (· + D) := by
    simp only [levels, hlen, hτlen, List.range_add, List.map_append, List.map_map]
    congr 2
    funext i
    simp only [Function.comp_def]
    omega
  have hsmallLevels (s : Side) (l : ℕ) (hl : 1 ≤ l) (hlD : l ≤ D) :
      π.levelsOn s l = τ.levelsOn s l := by
    unfold levelsOn
    rw [hlevels, List.filter_append]
    have hempty : (σ.levels.map (· + D)).filter
        (fun n => π.sideAt n = s ∧ (l = 0 ∨ n < l)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro n hn
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
      have hi1 := one_le_of_mem_levels hi
      simp only [decide_eq_true_eq]
      omega
    rw [hempty, List.append_nil]
    apply List.filter_congr
    intro n _
    rw [hτside]
  have hsmallLeft (s : Side) (l z : ℕ) (hl : 1 ≤ l) (hlD : l ≤ D) :
      π.leftExt s l z = τ.leftExt s l z := by
    rw [leftExt_eq, leftExt_eq, hsmallLevels s l hl hlD]
    rfl
  have hsmallRight (s : Side) (l z : ℕ) (hl : 1 ≤ l) (hlD : l ≤ D) :
      π.rightExt s l z = τ.rightExt s l z := by
    rw [rightExt_eq, rightExt_eq, hsmallLevels s l hl hlD]
    rfl
  have hchainExact (s : Side) :
      π.chainExt s p q = σ.chainExt s b b + τ.chainExt s p q := by
    have hL : π.leftExt s 0 p = τ.leftExt s 0 p + σ.leftExt s 0 b := hleftExact s 0 p hp
    have hR : π.rightExt s 0 q = τ.rightExt s 0 q + σ.rightExt s 0 b := hrightExact s 0 q hq
    unfold chainExt
    rw [hL, hR]
    omega
  have hjoinExact (s : Side) :
      π.joinExt s p q = max (σ.joinExt s b b + τ.chainExt s p q) (τ.joinExt s p q) := by
    have hdom : π.levelsOn s 0 = τ.levelsOn s 0 ++ (σ.levelsOn s 0).map (· + D) := by
      simpa only [if_pos rfl] using hsplitLevels s 0
    have hOldTerm (l : ℕ) (hl : l ∈ σ.levelsOn s 0) :
        σ.leftExt s l b + σ.rightExt s l b + σ.maximumAt l + τ.chainExt s p q ≤ π.joinExt s p q := by
      have hl1 := (one_le_of_mem_levelsOn hl).1
      have hmem : l + D ∈ π.levelsOn s 0 := by
        rw [hdom]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
      have hv := le_joinExt_of_mem_levelsOn hmem p q
      have hL := hleftExact s l p hp
      have hR := hrightExact s l q hq
      simp only [if_neg (by omega : l ≠ 0)] at hL hR
      rw [hL, hR, hmaximum l hl1] at hv
      unfold chainExt
      omega
    have hNewTerm (l : ℕ) (hl : l ∈ τ.levelsOn s 0) :
        τ.leftExt s l p + τ.rightExt s l q + τ.maximumAt l ≤ π.joinExt s p q := by
      have hlD := hτmem s 0 l hl
      have hmem : l ∈ π.levelsOn s 0 := by rw [hdom]; exact List.mem_append_left _ hl
      have hv := le_joinExt_of_mem_levelsOn hmem p q
      rw [hsmallLeft s l p hlD.1 hlD.2, hsmallRight s l q hlD.1 hlD.2,
        ← hτmaximum l hlD.1 hlD.2] at hv
      exact hv
    have hChainLe := π.chainExt_le_joinExt s p q
    have hTLe : τ.chainExt s p q ≤ π.joinExt s p q := by rw [hchainExact] at hChainLe; omega
    have hOldLe : σ.joinExt s b b + τ.chainExt s p q ≤ π.joinExt s p q := by
      let oldVals := (σ.levelsOn s 0).map
        (fun l => σ.leftExt s l b + σ.rightExt s l b + σ.maximumAt l)
      have hMaxOld : (oldVals.max?).getD 0 + τ.chainExt s p q ≤ π.joinExt s p q := by
        cases he : oldVals.max? with
        | none => simpa only [Option.getD_none, Nat.zero_add] using hTLe
        | some v =>
          obtain ⟨l, hl, heq⟩ := List.mem_map.mp (List.max?_mem he)
          have hv := hOldTerm l hl
          simp only [Option.getD_some]
          omega
      change max (σ.chainExt s b b) ((oldVals.max?).getD 0) + τ.chainExt s p q ≤ _
      rw [hchainExact] at hChainLe
      omega
    have hNewLe : τ.joinExt s p q ≤ π.joinExt s p q := by
      change max (τ.chainExt s p q) _ ≤ _
      apply max_le hTLe
      apply getD_max?_le
      intro v hv
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      exact hNewTerm l hl
    apply le_antisymm
    · change max (π.chainExt s p q) _ ≤ _
      apply max_le
      · have hc := σ.chainExt_le_joinExt s b b
        rw [hchainExact]
        omega
      · apply getD_max?_le
        intro v hv
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
        rw [hdom] at hl
        rcases List.mem_append.mp hl with hl | hl
        · have hlD := hτmem s 0 l hl
          rw [hsmallLeft s l p hlD.1 hlD.2, hsmallRight s l q hlD.1 hlD.2,
            ← hτmaximum l hlD.1 hlD.2]
          exact (le_joinExt_of_mem_levelsOn hl p q).trans (le_max_right _ _)
        · obtain ⟨oldLevel, hOldLevel, rfl⟩ := List.mem_map.mp hl
          have hOld1 := (one_le_of_mem_levelsOn hOldLevel).1
          have hL := hleftExact s oldLevel p hp
          have hR := hrightExact s oldLevel q hq
          simp only [if_neg (by omega : oldLevel ≠ 0)] at hL hR
          rw [hL, hR, hmaximum oldLevel hOld1]
          have hv := le_joinExt_of_mem_levelsOn hOldLevel b b
          have hMax : σ.joinExt s b b + τ.chainExt s p q ≤
              max (σ.joinExt s b b + τ.chainExt s p q) (τ.joinExt s p q) := le_max_left _ _
          have hT : τ.chainExt s p q = τ.leftExt s 0 p + τ.rightExt s 0 q := rfl
          omega
    · exact max_le hOldLe hNewLe
  constructor
  · change min (π.u - 1 - π.chainExt Side.lower p q) (π.k - 1 - π.joinExt Side.lower p q) =
      min (σ.cupLimit b b - τ.chainExt Side.lower p q) (π.k - 1 - τ.joinExt Side.lower p q)
    rw [hu, hk, hchainExact, hjoinExact]
    have hC : σ.cupLimit b b = min (σ.u - 1 - σ.chainExt Side.lower b b)
        (σ.k - 1 - σ.joinExt Side.lower b b) := rfl
    rw [hC]
    omega
  · change min (π.a - 1 - π.chainExt Side.upper p q) (π.k - 1 - π.joinExt Side.upper p q) =
      min (σ.capLimit b b - τ.chainExt Side.upper p q) (π.k - 1 - τ.joinExt Side.upper p q)
    rw [ha, hk, hchainExact, hjoinExact]
    have hP : σ.capLimit b b = min (σ.a - 1 - σ.chainExt Side.upper b b)
        (σ.k - 1 - σ.joinExt Side.upper b b) := rfl
    rw [hP]
    omega

end ErdosSzekeres
