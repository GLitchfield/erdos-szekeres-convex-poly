import ESBlueprint.B.CtxPartTrackedRankReservation

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- An occupied-color bound mixing clear unit classes with common singleton pure-rank classes, each on its independently chosen axis. Positive labels and unit chosen capacities apply only to source-active children. Clear-mode same-color active pairs have marker-clear intervals; rank-mode active children have a fixed common singleton pure rank. Every fuel approximation and the full recursive bound are at most the occupied-color count, which is additive across arbitrary disjoint lower/upper parts and new maxima. Global parameters and inactive children are arbitrary. Rank inheritance follows from old-extension monotonicity and part activity; tracked rank reservation excludes a shared rank-mode color across a cut. Removes the concrete clear-cover overcount with own global four and opposite global five, where two active children share singleton rank two across an intervening marker. Supplies the coincident-rank cover mechanism for the all-unit branch of the singleton-end sandwich mixed potential.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_mixed_clear_or_singleton_rank_cover_potential (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (color : ℕ → ℕ) (axis : ℕ → Ctx.Side)
  (rankMode : ℕ → Bool) (rank : ℕ → ℕ)
  (hunit : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    (match axis (color p) with
      | Ctx.Side.lower => σ.cupLimit p p
      | Ctx.Side.upper => σ.capLimit p p) ≤ 1)
  (hclear : ∀ p ∈ σ.childPositions, ∀ q ∈ σ.childPositions,
    0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    0 < σ.cupLimit q q → 0 < σ.capLimit q q → color p = color q →
    rankMode (color p) = false → ∀ j ∈ σ.levelsOn (axis (color p)) 0, ∀ x ∈ σ.extPositions j,
      x < min p q ∨ max p q < x)
  (hrank : ∀ p ∈ σ.childPositions, 0 < σ.cupLimit p p → 0 < σ.capLimit p p →
    rankMode (color p) = true →
    σ.leftExt (axis (color p)) 0 p + 1 = rank (color p) ∧
      rank (color p) + σ.rightExt (axis (color p)) 0 p =
        (fun v : Ctx.Side => match v with
          | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) (axis (color p)) - 1) :
  let active := fun (ρ : Ctx.Context) => ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let potential := fun (ρ : Ctx.Context) => ((active ρ).image color).card
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ potential σ) ∧ σ.bound ≤ potential σ ∧
    (∀ (keep rest : List ℕ) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      potential (σ.part keep Ctx.Side.lower m) +
        potential (σ.part rest Ctx.Side.upper n) ≤ potential σ) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (p : ℕ) := match v with
    | Side.lower => ρ.cupLimit p p
    | Side.upper => ρ.capLimit p p
  let active (ρ : Context) := ρ.childPositions.toFinset.filter
    (fun p => 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p)
  let marks (ρ : Context) (v : Side) :=
    (ρ.levelsOn v 0).toFinset.biUnion (fun j => (ρ.extPositions j).toFinset)
  let V (ρ : Context) := ((active ρ).image color).card
  let Good (ρ : Context) : Prop :=
    (∀ p ∈ active ρ, C ρ (axis (color p)) p ≤ 1) ∧
    (∀ p ∈ active ρ, ∀ q ∈ active ρ, color p = color q → rankMode (color p) = false →
      ∀ j ∈ ρ.levelsOn (axis (color p)) 0, ∀ x ∈ ρ.extPositions j,
        x < min p q ∨ max p q < x) ∧
    (∀ p ∈ active ρ, rankMode (color p) = true →
      ρ.leftExt (axis (color p)) 0 p + 1 = rank (color p) ∧
        rank (color p) + ρ.rightExt (axis (color p)) 0 p = G ρ (axis (color p)) - 1)
  change (∀ fuel, boundFuel fuel σ ≤ V σ) ∧ σ.bound ≤ V σ ∧
    (∀ (keep rest : List ℕ) (m n : ℕ),
      (∀ p ∈ σ.childPositions, p ∈ keep → p ∉ rest) →
      V (σ.part keep Side.lower m) + V (σ.part rest Side.upper n) ≤ V σ)
  have hActive (ρ : Context) (p : ℕ) : p ∈ active ρ ↔
      p ∈ ρ.childPositions ∧ 0 < ρ.cupLimit p p ∧ 0 < ρ.capLimit p p := by simp [active]
  have hMark (ρ : Context) (v : Side) (x : ℕ) :
      x ∈ marks ρ v ↔ ∃ j ∈ ρ.levelsOn v 0, x ∈ ρ.extPositions j := by simp [marks]
  have hPartActive (ρ : Context) (keep : List ℕ) (v : Side) (m p : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) : p ∈ active ρ ∧ p ∈ keep := by
    obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
    rw [part_childPositions] at hc
    obtain ⟨hc, hk⟩ := List.mem_filter.mp hc
    simp only [decide_eq_true_eq] at hk
    have hle := ctx_part_limits_le ρ keep v m p p
    exact ⟨(hActive _ _).mpr ⟨hc, by omega, by omega⟩, hk⟩
  have hPartMarks (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (w v : Side) (m x : ℕ) (hx : x ∈ marks (ρ.part keep w m) v) :
      x ∈ marks ρ v ∨ (w = v ∧ x ∈ ρ.childPositions ∧ x ∉ keep) := by
    obtain ⟨j, hj, hx⟩ := (hMark _ _ _).mp hx
    have hj' := List.mem_filter.mp hj
    have hs : (ρ.part keep w m).sideAt j = v := by simpa using hj'.2
    rw [part_levels] at hj'
    rcases List.mem_cons.mp hj'.1 with rfl | hold
    · right
      have hside := part_sideAt_one_of_mem hPos keep w m hx
      rw [part_extPositions_one hPos keep w m] at hx
      have hr := List.mem_filter.mp hx
      exact ⟨hside.symm.trans hs, hr.1, by simpa using hr.2⟩
    · left
      obtain ⟨i, hi, hij⟩ := List.mem_map.mp hold
      subst j
      have hi1 := one_le_of_mem_levels hi
      rw [part_extPositions_succ ρ keep w m hi1] at hx
      rw [part_sideAt_succ ρ keep w m hi1] at hs
      exact (hMark ρ v x).mpr ⟨i, by simp [Context.levelsOn, hi, hs], hx⟩
  have hExclude (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m p q : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) (hq : q ∈ ρ.childPositions) (hnot : q ∉ keep)
      (hUnit : C ρ v p ≤ 1)
      (hClear : ∀ j ∈ ρ.levelsOn v 0, ∀ x ∈ ρ.extPositions j,
        x < min p q ∨ max p q < x) : False := by
    have hpa := hPartActive ρ keep v m p hp
    have hpc := ((hActive ρ p).mp hpa.1).1
    have hd := (ctx_part_capacity_drop_in_clear_interval ρ hPos keep v m p q
      hpc hpa.2 hq hnot hClear).2.2
    have hpp := (hActive _ _).mp hp
    cases v <;> dsimp only [C] at hUnit hd <;> omega
  have hInherit (ρ : Context) (keep : List ℕ) (v : Side) (m : ℕ) (u : Side) (p : ℕ) :
      ρ.leftExt u 0 p ≤ (ρ.part keep v m).leftExt u 0 p ∧
      ρ.rightExt u 0 p ≤ (ρ.part keep v m).rightExt u 0 p := by
    let τ := ρ.part keep v m
    have hlevels (t : Ctx.Side) (N : ℕ) :
        List.Sublist ((ρ.levelsOn t N).map (· + 1)) (τ.levelsOn t (if N = 0 then 0 else N + 1)) := by
      unfold Ctx.Context.levelsOn
      change List.Sublist _ ((ρ.part keep v m).levels.filter _)
      rw [Ctx.Context.part_levels, List.filter_cons, List.filter_map]
      have heq : ρ.levels.filter (fun l => decide ((ρ.part keep v m).sideAt (l + 1) = t ∧
          ((if N = 0 then 0 else N + 1) = 0 ∨ l + 1 < (if N = 0 then 0 else N + 1)))) =
          ρ.levels.filter (fun l => decide (ρ.sideAt l = t ∧ (N = 0 ∨ l < N))) := by
        apply List.filter_congr
        intro l hl
        have hl1 := Ctx.Context.one_le_of_mem_levels hl
        by_cases hN : N = 0 <;>
          simp [hN, Ctx.Context.part_sideAt_succ ρ keep v m hl1]
      simp only [Function.comp_def]
      rw [heq]
      split_ifs <;> simp_all
    have hleft (t : Ctx.Side) (N p : ℕ) :
        ρ.leftExt t N p ≤ τ.leftExt t (if N = 0 then 0 else N + 1) p := by
      simp only [Ctx.Context.leftExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      have hsub := List.mem_sublists.mp hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
      refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.leftStep τ) (p, 0)).2,
        List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_leftStep_part_map ρ keep v m ls hpos (p, 0))).symm
    have hright (t : Ctx.Side) (N p : ℕ) :
        ρ.rightExt t N p ≤ τ.rightExt t (if N = 0 then 0 else N + 1) p := by
      simp only [Ctx.Context.rightExt_eq]
      apply Ctx.getD_max?_le_of_forall
      intro x hx
      obtain ⟨ls, hls, rfl⟩ := List.mem_map.mp hx
      have hsub := List.mem_sublists.mp hls
      have hpos : ∀ l ∈ ls, 1 ≤ l := fun l hl =>
        (Ctx.Context.one_le_of_mem_levelsOn (hsub.subset hl)).1
      refine ⟨((ls.map (· + 1)).foldl (Ctx.Context.rightStep τ) (p, 0)).2,
        List.mem_map.mpr ⟨_, List.mem_sublists.mpr ((hsub.map _).trans (hlevels t N)), rfl⟩, ?_⟩
      exact le_of_eq (congrArg Prod.snd (Ctx.Context.foldl_rightStep_part_map ρ keep v m ls hpos (p, 0))).symm
    exact ⟨by simpa only [if_pos rfl] using hleft u 0 p,
      by simpa only [if_pos rfl] using hright u 0 p⟩
  have hPure (ρ : Context) (v : Side) (p : ℕ) (hp : p ∈ active ρ) :
      ρ.leftExt v 0 p + ρ.rightExt v 0 p < G ρ v - 1 := by
    have hh := ((hActive ρ p).mp hp).2
    cases v <;> simp only [G, cupLimit, capLimit, chainExt] at hh ⊢ <;> omega
  have hExcludeRank (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (keep : List ℕ) (v : Side) (m p q r : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) (hq : q ∈ active ρ) (hnot : q ∉ keep)
      (hrp : ρ.leftExt v 0 p + 1 = r ∧ r + ρ.rightExt v 0 p = G ρ v - 1)
      (hrq : ρ.leftExt v 0 q + 1 = r ∧ r + ρ.rightExt v 0 q = G ρ v - 1) : False := by
    let τ := ρ.part keep v m
    let F : Finset ℕ := {p, q}
    let Q : Finset ℕ := {p}
    let L := ({q} : Finset ℕ).filter (· < p)
    let R := ({q} : Finset ℕ).filter (p < ·)
    let I (η : Context) (x : ℕ) := Finset.Icc (η.leftExt v 0 x + 1) (G η v - 1 - η.rightExt v 0 x)
    let S := F.biUnion (I ρ)
    let T := Q.biUnion (I τ)
    let E := (L.image (fun x => ρ.leftExt v 0 x + 1)) ∪
      (R.image (fun x => G ρ v - 1 - ρ.rightExt v 0 x))
    have hpa := hPartActive ρ keep v m p hp
    have hpq : p ≠ q := by intro he; subst p; exact hnot hpa.2
    have hF : ∀ x ∈ F, x ∈ ρ.childPositions ∧ 0 < ρ.cupLimit x x ∧ 0 < ρ.capLimit x x := by
      intro x hx
      simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (hActive _ _).mp hpa.1
      · exact (hActive _ _).mp hq
    have hQ : ∀ x ∈ Q, x ∈ τ.childPositions ∧ 0 < τ.cupLimit x x ∧ 0 < τ.capLimit x x := by
      intro x hx
      have he : x = p := Finset.mem_singleton.mp hx
      subst x
      exact (hActive τ p).mp hp
    have hQF : Q ⊆ F := by
      intro x hx
      have he : x = p := Finset.mem_singleton.mp hx
      subst x
      simp [F]
    have hL : ∀ x ∈ L, x ∈ F ∧ x ∉ keep := by
      intro x hx
      have he : x = q := Finset.mem_singleton.mp (Finset.mem_filter.mp hx).1
      subst x
      exact ⟨by simp [F], hnot⟩
    have hR : ∀ x ∈ R, x ∈ F ∧ x ∉ keep := by
      intro x hx
      have he : x = q := Finset.mem_singleton.mp (Finset.mem_filter.mp hx).1
      subst x
      exact ⟨by simp [F], hnot⟩
    have hleft : ∀ x ∈ L, ∀ y ∈ Q, x < y := by
      intro x hx y hy
      have he : y = p := Finset.mem_singleton.mp hy
      subst y
      exact (Finset.mem_filter.mp hx).2
    have hright : ∀ x ∈ R, ∀ y ∈ Q, y < x := by
      intro x hx y hy
      have he : y = p := Finset.mem_singleton.mp hy
      subst y
      exact (Finset.mem_filter.mp hx).2
    have hLoss := ctx_part_tracked_rank_reservation ρ hPos v keep m F Q L R hF hQ hQF hL hR hleft hright
    have hCard : T.card + E.card ≤ S.card := hLoss.2.2.1
    have hIp : I ρ p = {r} := by
      change Finset.Icc (ρ.leftExt v 0 p + 1) (G ρ v - 1 - ρ.rightExt v 0 p) = {r}
      rw [hrp.1, show G ρ v - 1 - ρ.rightExt v 0 p = r by omega]
      exact Finset.Icc_self r
    have hIq : I ρ q = {r} := by
      change Finset.Icc (ρ.leftExt v 0 q + 1) (G ρ v - 1 - ρ.rightExt v 0 q) = {r}
      rw [hrq.1, show G ρ v - 1 - ρ.rightExt v 0 q = r by omega]
      exact Finset.Icc_self r
    have hS : S.card = 1 := by simp [S, F, hIp, hIq]
    have hE : E.Nonempty := by
      by_cases hqp : q < p
      · refine ⟨ρ.leftExt v 0 q + 1, Finset.mem_union.mpr (Or.inl ?_)⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨by simp, hqp⟩, rfl⟩
      · refine ⟨G ρ v - 1 - ρ.rightExt v 0 q, Finset.mem_union.mpr (Or.inr ?_)⟩
        exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨by simp, by omega⟩, rfl⟩
    have hT : T.Nonempty := by
      have hpos := hPure τ v p hp
      refine ⟨τ.leftExt v 0 p + 1, Finset.mem_biUnion.mpr ⟨p, by simp [Q], ?_⟩⟩
      exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have he := Finset.card_pos.mpr hE
    have ht := Finset.card_pos.mpr hT
    omega
  have hGoodPart (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hg : Good ρ) (keep : List ℕ) (w : Side) (m : ℕ) : Good (ρ.part keep w m) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      have hpa := hPartActive ρ keep w m p hp
      have hu := hg.1 p hpa.1
      have hle := ctx_part_limits_le ρ keep w m p p
      cases hv : axis (color p) <;> simp only [hv, C] at hu ⊢ <;> omega
    · intro p hp q hq he hm j hj x hx
      have hpa := hPartActive ρ keep w m p hp
      have hqa := hPartActive ρ keep w m q hq
      have hc := hg.2.1 p hpa.1 q hqa.1 he hm
      have hxm : x ∈ marks (ρ.part keep w m) (axis (color p)) :=
        (hMark _ _ _).mpr ⟨j, hj, hx⟩
      rcases hPartMarks ρ hPos keep w (axis (color p)) m x hxm with hold | ⟨hw, hxc, hxn⟩
      · obtain ⟨i, hi, hxi⟩ := (hMark _ _ _).mp hold
        exact hc i hi x hxi
      · by_contra hout
        apply hExclude ρ hPos keep w m p x hp hxc hxn
        · rw [hw]
          exact hg.1 p hpa.1
        · intro i hi y hy
          rw [hw] at hi
          have hh := hc i hi y hy
          omega
    · intro p hp hm
      let v := axis (color p)
      have hpa := hPartActive ρ keep w m p hp
      have hr := hg.2.2 p hpa.1 hm
      have hi := hInherit ρ keep w m v p
      have hpos := hPure (ρ.part keep w m) v p hp
      have hG : G (ρ.part keep w m) v = G ρ v := by cases v <;> rfl
      change ρ.leftExt v 0 p + 1 = rank (color p) ∧
        rank (color p) + ρ.rightExt v 0 p = G ρ v - 1 at hr
      change (ρ.part keep w m).leftExt v 0 p + 1 = rank (color p) ∧
        rank (color p) + (ρ.part keep w m).rightExt v 0 p = G (ρ.part keep w m) v - 1
      rw [hG] at hpos ⊢
      constructor <;> omega
  have hExcludeColor (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hg : Good ρ) (keep : List ℕ) (v : Side) (m p q : ℕ)
      (hp : p ∈ active (ρ.part keep v m)) (hq : q ∈ active ρ) (hnot : q ∉ keep)
      (hv : v = axis (color p)) (he : color q = color p) : False := by
    have hpa := (hPartActive ρ keep v m p hp).1
    cases hm : rankMode (color p) with
    | false =>
      apply hExclude ρ hPos keep v m p q hp ((hActive ρ q).mp hq).1 hnot
      · rw [hv]
        exact hg.1 p hpa
      · rw [hv]
        exact hg.2.1 p hpa q hq he.symm hm
    | true =>
      have hrp := hg.2.2 p hpa hm
      have hmQ : rankMode (color q) = true := by rw [he]; exact hm
      have hrq := hg.2.2 q hq hmQ
      simp only [he, G] at hrq
      apply hExcludeRank ρ hPos keep v m p q (rank (color p)) hp hq hnot
      · rw [hv]
        exact hrp
      · rw [hv]
        exact hrq
  have hCut (ρ : Context)
      (hPos : ∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j)
      (hg : Good ρ) (keep rest : List ℕ) (m n : ℕ)
      (hdis : ∀ p ∈ ρ.childPositions, p ∈ keep → p ∉ rest) :
      V (ρ.part keep Side.lower m) + V (ρ.part rest Side.upper n) ≤ V ρ := by
    let A := active (ρ.part keep Side.lower m)
    let B := active (ρ.part rest Side.upper n)
    have hab : Disjoint (A.image color) (B.image color) := by
      apply Finset.disjoint_left.mpr
      intro z hzA hzB
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hzA
      obtain ⟨q, hq, hqp⟩ := Finset.mem_image.mp hzB
      have hpa := hPartActive ρ keep Side.lower m p hp
      have hqa := hPartActive ρ rest Side.upper n q hq
      have hpc := ((hActive _ _).mp hpa.1).1
      have hqc := ((hActive _ _).mp hqa.1).1
      have hqnot : q ∉ keep := fun hk => hdis q hqc hk hqa.2
      have hpnot : p ∉ rest := hdis p hpc hpa.2
      cases hv : axis (color p) with
      | lower =>
        exact hExcludeColor ρ hPos hg keep Side.lower m p q hp hqa.1 hqnot hv.symm hqp
      | upper =>
        have hvq : axis (color q) = Side.upper := by rw [hqp]; exact hv
        exact hExcludeColor ρ hPos hg rest Side.upper n q p hq hpa.1 hpnot hvq.symm hqp.symm
    have hsub : A.image color ∪ B.image color ⊆ (active ρ).image color := by
      intro z hz
      rcases Finset.mem_union.mp hz with ha | hb
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_image.mpr ⟨p, (hPartActive ρ keep Side.lower m p hp).1, rfl⟩
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
        exact Finset.mem_image.mpr ⟨q, (hPartActive ρ rest Side.upper n q hq).1, rfl⟩
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hab] at hh
    exact hh
  have hPositivePart (ρ : Context) (keep : List ℕ) (t : Side) (m : ℕ) :
      ∀ x j v, (ρ.part keep t m).letterAt x = Letter.ext j v → 1 ≤ j := by
    intro x j v hx
    have hxl : x < ρ.word.length := by
      by_contra h
      have hn := letterAt_of_length_le (ρ.part keep t m)
        (show (ρ.part keep t m).word.length ≤ x by rw [part_word_length]; omega)
      rw [hn] at hx
      cases hx
    cases he : ρ.letterAt x with
    | child =>
      rw [part_letterAt_of_child ρ keep t m hxl he] at hx
      split at hx
      · cases hx
      · cases hx; omega
    | ext oldLevel oldSide =>
      rw [part_letterAt_of_ext ρ keep t m hxl he] at hx
      cases hx; omega
  have hBase (ρ : Context) (hg : Good ρ) : ρ.base ≤ V ρ := by
    rw [base_eq_baseOf]
    cases hh : ρ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr hh)
      change baseOf (ρ.cupLimit p p) (ρ.capLimit p p) ρ.k ≤ V ρ
      by_cases hz : ρ.cupLimit p p = 0 ∨ ρ.capLimit p p = 0
      · simp [baseOf, hz]
      have hpa : p ∈ active ρ := (hActive _ _).mpr ⟨hp, by omega, by omega⟩
      have hu := hg.1 p hpa
      have hone : ρ.cupLimit p p = 1 ∨ ρ.capLimit p p = 1 := by
        cases hv : axis (color p) <;> simp only [hv, C] at hu <;> omega
      have hn : ((active ρ).image color).Nonempty := ⟨color p, Finset.mem_image.mpr ⟨p, hpa, rfl⟩⟩
      simpa only [baseOf, if_neg hz, if_pos hone] using Finset.card_pos.mpr hn
  have hFuel : ∀ fuel (ρ : Context),
      (∀ x j v, ρ.letterAt x = Letter.ext j v → 1 ≤ j) → Good ρ → boundFuel fuel ρ ≤ V ρ := by
    intro fuel
    induction fuel with
    | zero => intro ρ _ _; exact Nat.zero_le _
    | succ fuel ih =>
      intro ρ hPos hg
      rw [boundFuel]
      split
      · exact hBase ρ hg
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, _, d, _, hz⟩ := hz
        have hparts (ks : List ℕ) (v : Side) (c : ℕ) :
            boundFuel fuel (ρ.part ks v c) ≤ V (ρ.part ks v c) :=
          ih _ (hPositivePart ρ ks v c) (hGoodPart ρ hPos hg ks v c)
        rcases hz with rfl | rfl
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          apply hCut ρ hPos hg
          intro p _ hp hr
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hr).2
          exact hn hp
        · apply (Nat.add_le_add (hparts _ _ _) (hparts _ _ _)).trans
          rw [Nat.add_comm]
          apply hCut ρ hPos hg
          intro p _ hp hk
          have hn : p ∉ keep := by simpa using (List.mem_filter.mp hp).2
          exact hn hk
  have hOurGood : Good σ := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
      exact hunit p hc hcup hcap
    · intro p hp q hq he hm
      obtain ⟨hpc, hpcup, hpcap⟩ := (hActive _ _).mp hp
      obtain ⟨hqc, hqcup, hqcap⟩ := (hActive _ _).mp hq
      exact hclear p hpc q hqc hpcup hpcap hqcup hqcap he hm
    · intro p hp hm
      obtain ⟨hc, hcup, hcap⟩ := (hActive _ _).mp hp
      exact hrank p hc hcup hcap hm
  exact ⟨fun fuel => hFuel fuel σ hpositive hOurGood, hFuel _ σ hpositive hOurGood,
    fun keep rest m n hdis => hCut σ hpositive hOurGood keep rest m n hdis⟩


end ErdosSzekeres
