import ErdosSzekeres.DecomposableContextLemmas
import ESBlueprint.B.CtxBoundCutLe

namespace ErdosSzekeres

open Ctx Ctx.Context

/-! ### Lists: a nonempty list attains its maximum -/

theorem foldl_max_mem (zs : List ℕ) : ∀ z : ℕ, zs.foldl max z ∈ z :: zs := by
  induction zs with
  | nil => intro z; simp
  | cons w ws ih =>
    intro z
    have h := ih (max z w)
    simp only [List.foldl_cons]
    rcases le_total z w with hzw | hwz
    · rw [max_eq_right hzw] at h ⊢
      exact List.mem_cons.2 (Or.inr h)
    · rw [max_eq_left hwz] at h ⊢
      rcases List.mem_cons.1 h with h | h
      · exact List.mem_cons.2 (Or.inl h)
      · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr h)))

theorem exists_mem_eq_getD_max? (L : List ℕ) (hL : L ≠ []) : ∃ x ∈ L, (L.max?).getD 0 = x := by
  cases L with
  | nil => exact absurd rfl hL
  | cons x xs =>
    refine ⟨xs.foldl max x, foldl_max_mem xs x, ?_⟩
    simp only [List.max?_cons', Option.getD_some]

namespace Ctx.Context

/-! ### The recursion stabilizes once the fuel exceeds the number of child letters -/

theorem part_childPositions_length_lt_of_mem_blocks {σ : Context} {block : List ℕ} (hb : block ∈ σ.blocks) (s : Side) (m : ℕ) :
    (σ.part block s m).childPositions.length < σ.childPositions.length := by
  obtain ⟨hblen, _, _⟩ := mem_blocks hb
  rw [part_childPositions]
  exact lt_of_le_of_lt (length_filter_mem_le (block := block) (childPositions_nodup σ)) hblen

theorem part_rest_childPositions_length_lt_of_mem_blocks {σ : Context} {block : List ℕ} (hb : block ∈ σ.blocks) (s : Side) (m : ℕ) :
    (σ.part (σ.childPositions.filter (fun p => p ∉ block)) s m).childPositions.length < σ.childPositions.length := by
  obtain ⟨_, hbne, hbsub⟩ := mem_blocks hb
  rw [part_childPositions]
  have heq : σ.childPositions.filter (· ∈ σ.childPositions.filter (fun p => p ∉ block)) =
      σ.childPositions.filter (· ∉ block) := by
    apply List.filter_congr
    intro p hp
    simp [hp]
  rw [heq]
  exact length_filter_not_mem_lt hbne hbsub

/-- With fuel at least the child count plus one, the recursion no longer depends on the fuel. -/
theorem boundFuel_stable : ∀ (n : ℕ) (σ : Context), σ.childPositions.length = n →
    ∀ f₁ f₂, n + 1 ≤ f₁ → n + 1 ≤ f₂ → boundFuel f₁ σ = boundFuel f₂ σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hn f₁ f₂ h₁ h₂
    obtain ⟨g₁, rfl⟩ : ∃ g, f₁ = g + 1 := ⟨f₁ - 1, by omega⟩
    obtain ⟨g₂, rfl⟩ : ∃ g, f₂ = g + 1 := ⟨f₂ - 1, by omega⟩
    rw [boundFuel.eq_2 σ g₁, boundFuel.eq_2 σ g₂]
    split_ifs with hruns
    · rfl
    · dsimp only
      have hpart : ∀ (keep : List ℕ) (s : Side) (m : ℕ),
          (σ.part keep s m).childPositions.length < n →
          boundFuel g₁ (σ.part keep s m) = boundFuel g₂ (σ.part keep s m) := by
        intro keep s m hlt
        exact ih _ hlt _ rfl g₁ g₂ (by omega) (by omega)
      apply le_antisymm
      · apply getD_max?_le_of_forall
        intro x hx
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        obtain ⟨block, hb, d', hd', hx⟩ := hx
        rcases hx with rfl | rfl
        · refine ⟨_, ⟨block, hb, d', hd', Or.inl rfl⟩, ?_⟩
          rw [hpart _ _ _ (hn ▸ part_childPositions_length_lt_of_mem_blocks hb _ _),
            hpart _ _ _ (hn ▸ part_rest_childPositions_length_lt_of_mem_blocks hb _ _)]
        · refine ⟨_, ⟨block, hb, d', hd', Or.inr rfl⟩, ?_⟩
          rw [hpart _ _ _ (hn ▸ part_childPositions_length_lt_of_mem_blocks hb _ _),
            hpart _ _ _ (hn ▸ part_rest_childPositions_length_lt_of_mem_blocks hb _ _)]
      · apply getD_max?_le_of_forall
        intro x hx
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        obtain ⟨block, hb, d', hd', hx⟩ := hx
        rcases hx with rfl | rfl
        · refine ⟨_, ⟨block, hb, d', hd', Or.inl rfl⟩, ?_⟩
          rw [hpart _ _ _ (hn ▸ part_childPositions_length_lt_of_mem_blocks hb _ _),
            hpart _ _ _ (hn ▸ part_rest_childPositions_length_lt_of_mem_blocks hb _ _)]
        · refine ⟨_, ⟨block, hb, d', hd', Or.inr rfl⟩, ?_⟩
          rw [hpart _ _ _ (hn ▸ part_childPositions_length_lt_of_mem_blocks hb _ _),
            hpart _ _ _ (hn ▸ part_rest_childPositions_length_lt_of_mem_blocks hb _ _)]

theorem boundFuel_eq_bound (σ : Context) {f : ℕ} (hf : σ.childPositions.length + 1 ≤ f) :
    boundFuel f σ = σ.bound :=
  boundFuel_stable _ σ rfl f _ hf le_rfl

/-! ### Two runs force an external letter, hence `3 ≤ k` -/

theorem exists_run_start_pos {σ : Context} (hruns : 2 ≤ σ.numRuns) :
    ∃ p, σ.letterAt p = Letter.child ∧ p ≠ 0 ∧ σ.letterAt (p - 1) ≠ Letter.child := by
  unfold numRuns at hruns
  set L := (List.range σ.word.length).filter fun p =>
    σ.letterAt p = Letter.child ∧ (p = 0 ∨ σ.letterAt (p - 1) ≠ Letter.child) with hL
  have hnodup : L.Nodup := List.Nodup.filter _ (List.nodup_range ..)
  have hmem : ∀ p ∈ L, σ.letterAt p = Letter.child ∧ (p = 0 ∨ σ.letterAt (p - 1) ≠ Letter.child) := by
    intro p hp
    have := (List.mem_filter.1 hp).2
    simpa using this
  -- a nodup list of length at least two has a member other than 0
  have hex : ∃ p ∈ L, p ≠ 0 := by
    by_contra hcon
    have hall : ∀ p ∈ L, p = 0 := fun p hp => by
      by_contra h
      exact hcon ⟨p, hp, h⟩
    have hsub : L ⊆ [0] := fun p hp => by simp [hall p hp]
    have hlen := (hnodup.subperm hsub).length_le
    simp at hlen
    omega
  obtain ⟨p, hp, hp0⟩ := hex
  have hp' := hmem p hp
  exact ⟨p, hp'.1, hp0, hp'.2.resolve_left hp0⟩

theorem three_le_k_of_two_runs {σ : Context} (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns) : 3 ≤ σ.k := by
  obtain ⟨p, _, hp0, hprev⟩ := exists_run_start_pos hruns
  cases hlet : σ.letterAt (p - 1) with
  | child => exact absurd hlet hprev
  | ext l s =>
    obtain ⟨hl1, hl2, _⟩ := hwf.2.2.2.2.2 (p - 1) l s hlet
    have hne : σ.maxima ≠ [] := by
      intro h
      rw [h] at hl2
      simp at hl2
      omega
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil σ.maxima hne
    have := hwf.2.2.2.2.1 m hm
    omega

/-! ### Parts depend on the kept list only through membership of child positions -/

theorem part_congr (σ : Context) {keep₁ keep₂ : List ℕ} (s : Side) (m : ℕ)
    (h : ∀ p ∈ σ.childPositions, p ∈ keep₁ ↔ p ∈ keep₂) : σ.part keep₁ s m = σ.part keep₂ s m := by
  unfold part
  congr 1
  apply List.map_congr_left
  intro p hp
  cases hl : σ.letterAt p with
  | child =>
    have hpc : p ∈ σ.childPositions := by
      unfold childPositions
      exact List.mem_filter.2 ⟨hp, by simp [hl]⟩
    simp [h p hpc]
  | ext l s' => rfl

/-- The block of a cut, as a window of the child positions. -/
theorem exists_take_drop_of_mem_blocks {σ : Context} {block : List ℕ} (hb : block ∈ σ.blocks) :
    ∃ i l, i < σ.childPositions.length ∧ l < σ.childPositions.length - i ∧
      block = (σ.childPositions.drop i).take (l + 1) := by
  unfold blocks at hb
  simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, decide_eq_true_eq] at hb
  obtain ⟨⟨i, hi, l, hl, rfl⟩, _⟩ := hb
  exact ⟨i, l, hi, hl, rfl⟩

end Ctx.Context

/-- Interior cuts: the block is neither the first nor the last child position alone, nor the
complement of one of them.  Every such cut is dominated by an end cut in one of the two forms;
this is the strip inequality (experiment 0124 §4). -/
theorem ctx_interior_cut_le_end_cut (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns)
    (block : List ℕ) (hb : block ∈ σ.blocks)
    (hfirst : ∀ p₀, σ.childPositions.head? = some p₀ →
      ¬ (∀ p ∈ σ.childPositions, p ∈ block ↔ p = p₀) ∧ ¬ (∀ p ∈ σ.childPositions, p ∈ block ↔ p ≠ p₀))
    (hlast : ∀ pₙ, σ.childPositions.getLast? = some pₙ →
      ¬ (∀ p ∈ σ.childPositions, p ∈ block ↔ p = pₙ) ∧ ¬ (∀ p ∈ σ.childPositions, p ∈ block ↔ p ≠ pₙ))
    (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) (v : ℕ)
    (hv : v = (σ.part block Ctx.Side.lower d).bound +
        (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨
      v = (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.lower d).bound) :
    ∃ p ∈ σ.childPositions, ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) ∧
      ∃ d', 1 ≤ d' ∧ d' ≤ σ.k - 2 ∧
        (v ≤ (σ.part [p] Ctx.Side.lower d').bound +
            (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d')).bound ∨
          v ≤ (σ.part [p] Ctx.Side.upper (σ.k - 1 - d')).bound +
            (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d').bound) := by
  sorry

/-- A cut whose block is, by membership, the first (or last) child position alone or its complement
is itself an end cut in one of the two forms. -/
theorem ctx_end_block_cut_le (σ : Ctx.Context) (block : List ℕ) (p : ℕ) (hp : p ∈ σ.childPositions)
    (hend : (∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p))
    (hblock : (∀ q ∈ σ.childPositions, q ∈ block ↔ q = p) ∨ (∀ q ∈ σ.childPositions, q ∈ block ↔ q ≠ p))
    (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) (v : ℕ)
    (hv : v = (σ.part block Ctx.Side.lower d).bound +
        (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨
      v = (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.lower d).bound) :
    ∃ p ∈ σ.childPositions, ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) ∧
      ∃ d', 1 ≤ d' ∧ d' ≤ σ.k - 2 ∧
        (v ≤ (σ.part [p] Ctx.Side.lower d').bound +
            (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d')).bound ∨
          v ≤ (σ.part [p] Ctx.Side.upper (σ.k - 1 - d')).bound +
            (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d').bound) := by
  refine ⟨p, hp, hend, d, hd, hdk, ?_⟩
  rcases hblock with hsame | hcompl
  · -- the block is the singleton {p}: the cut is the end cut itself
    have h1 : ∀ s m, σ.part block s m = σ.part [p] s m := fun s m =>
      part_congr σ s m fun q hq => by simp [hsame q hq]
    have h2 : ∀ s m, σ.part (σ.childPositions.filter (fun q => q ∉ block)) s m =
        σ.part (σ.childPositions.filter (fun q => q ≠ p)) s m := fun s m =>
      part_congr σ s m fun q hq => by simp [List.mem_filter, hq, hsame q hq]
    rcases hv with rfl | rfl
    · left; rw [h1, h2]
    · right; rw [h1, h2]
  · -- the block is everything but p: the cut is the end cut with the roles exchanged
    have h1 : ∀ s m, σ.part block s m = σ.part (σ.childPositions.filter (fun q => q ≠ p)) s m := fun s m =>
      part_congr σ s m fun q hq => by simp [List.mem_filter, hq, hcompl q hq]
    have h2 : ∀ s m, σ.part (σ.childPositions.filter (fun q => q ∉ block)) s m = σ.part [p] s m := fun s m =>
      part_congr σ s m fun q hq => by simp [List.mem_filter, hq, hcompl q hq]
    rcases hv with rfl | rfl
    · right; rw [h1, h2, Nat.add_comm]
    · left; rw [h1, h2, Nat.add_comm]

/-- The content: every interval cut of a context with at least two runs is dominated by a cut that
isolates the first or the last child position, on some side at some coupling. -/
theorem ctx_cut_le_end_cut (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns)
    (block : List ℕ) (hb : block ∈ σ.blocks) (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ σ.k - 2) (v : ℕ)
    (hv : v = (σ.part block Ctx.Side.lower d).bound +
        (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨
      v = (σ.part block Ctx.Side.upper (σ.k - 1 - d)).bound +
        (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Ctx.Side.lower d).bound) :
    ∃ p ∈ σ.childPositions, ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) ∧
      ∃ d', 1 ≤ d' ∧ d' ≤ σ.k - 2 ∧
        (v ≤ (σ.part [p] Ctx.Side.lower d').bound +
            (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d')).bound ∨
          v ≤ (σ.part [p] Ctx.Side.upper (σ.k - 1 - d')).bound +
            (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d').bound) := by
  have hlen : 2 ≤ σ.childPositions.length := le_trans hruns (numRuns_le_length σ)
  have hsorted := childPositions_pairwise σ
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, σ.childPositions.head? = some p₀ := by
    cases h : σ.childPositions with
    | nil => rw [h] at hlen; simp at hlen
    | cons x xs => exact ⟨x, rfl⟩
  obtain ⟨pₙ, hpₙ⟩ : ∃ pₙ, σ.childPositions.getLast? = some pₙ := by
    cases h : σ.childPositions with
    | nil => rw [h] at hlen; simp at hlen
    | cons x xs => exact ⟨(x :: xs).getLast (by simp), List.getLast?_eq_some_getLast (by simp)⟩
  have hp₀mem : p₀ ∈ σ.childPositions := List.mem_of_mem_head? hp₀
  have hpₙmem : pₙ ∈ σ.childPositions := List.mem_of_mem_getLast? hpₙ
  have hp₀le : ∀ q ∈ σ.childPositions, p₀ ≤ q := by
    intro q hq
    cases h : σ.childPositions with
    | nil => rw [h] at hq; simp at hq
    | cons x xs =>
      rw [h] at hp₀ hq hsorted
      simp only [List.head?_cons, Option.some.injEq] at hp₀
      subst hp₀
      rcases List.mem_cons.1 hq with rfl | hq
      · exact le_rfl
      · exact le_of_lt ((List.pairwise_cons.1 hsorted).1 q hq)
  have hpₙge : ∀ q ∈ σ.childPositions, q ≤ pₙ := by
    intro q hq
    have hsplit := List.dropLast_append_getLast (l := σ.childPositions) (by
      intro h; rw [h] at hlen; simp at hlen)
    rw [List.getLast?_eq_some_getLast (by intro h; rw [h] at hlen; simp at hlen), Option.some.injEq] at hpₙ
    rw [← hsplit, hpₙ] at hq hsorted
    rw [List.pairwise_append] at hsorted
    rcases List.mem_append.1 hq with hq | hq
    · exact le_of_lt (hsorted.2.2 q hq _ (List.mem_singleton_self _))
    · rw [List.mem_singleton] at hq; rw [hq]
  by_cases hE : (∀ q ∈ σ.childPositions, q ∈ block ↔ q = p₀) ∨ (∀ q ∈ σ.childPositions, q ∈ block ↔ q ≠ p₀)
  · exact ctx_end_block_cut_le σ block p₀ hp₀mem (Or.inl hp₀le) hE d hd hdk v hv
  by_cases hE' : (∀ q ∈ σ.childPositions, q ∈ block ↔ q = pₙ) ∨ (∀ q ∈ σ.childPositions, q ∈ block ↔ q ≠ pₙ)
  · exact ctx_end_block_cut_le σ block pₙ hpₙmem (Or.inr hpₙge) hE' d hd hdk v hv
  · refine ctx_interior_cut_le_end_cut σ hwf hruns block hb ?_ ?_ d hd hdk v hv
    · intro q hq
      rw [hp₀, Option.some.injEq] at hq
      subst hq
      exact ⟨fun h => hE (Or.inl h), fun h => hE (Or.inr h)⟩
    · intro q hq
      rw [hpₙ, Option.some.injEq] at hq
      subst hq
      exact ⟨fun h => hE' (Or.inl h), fun h => hE' (Or.inr h)⟩

/-- End-cut normal form for the context bound (experiment 0124 §2c): for a well-formed context with at least two child runs, the bound, which is the maximum over all interval cuts, is attained by a cut that isolates the first or the last child position, on some side at some admissible coupling. Interior blocks never win. Consequences: bound has a recursion over end cuts only, every cut tree normalizes to a sequence of end strips, and the exchange lemma behind additivity (the two-run boundary domination) becomes a commutation of two end strips. Evidence: every one of the 2,600 contexts with two or three runs and nonzero bound at k = 6 with up to four letters and two levels; the falsifier re-checks five cases.
@node
@ws B
@kind conjecture
@depends ErdosSzekeres.ctx_bound_cut_le
@consumer ErdosSzekeres.ctx_bound_two_run_boundary_domination
@falsifier ctx_end_cut_normal_form.py -/
theorem ctx_bound_attained_by_end_cut (σ : Ctx.Context) (hwf : σ.WellFormed) (hruns : 2 ≤ σ.numRuns) : ∃ p ∈ σ.childPositions, ((∀ q ∈ σ.childPositions, p ≤ q) ∨ (∀ q ∈ σ.childPositions, q ≤ p)) ∧ ∃ d, 1 ≤ d ∧ d ≤ σ.k - 2 ∧ (σ.bound ≤ (σ.part [p] Ctx.Side.lower d).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.upper (σ.k - 1 - d)).bound ∨ σ.bound ≤ (σ.part [p] Ctx.Side.upper (σ.k - 1 - d)).bound + (σ.part (σ.childPositions.filter (fun q => q ≠ p)) Ctx.Side.lower d).bound) := by
  have hk := three_le_k_of_two_runs hwf hruns
  have hlen : 2 ≤ σ.childPositions.length := le_trans hruns (numRuns_le_length σ)
  -- a first block: the first child position alone
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, σ.childPositions.head? = some p₀ := by
    cases h : σ.childPositions with
    | nil => rw [h] at hlen; simp at hlen
    | cons x xs => exact ⟨x, rfl⟩
  have hb₀ : [p₀] ∈ σ.blocks := by
    unfold blocks
    simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, decide_eq_true_eq]
    refine ⟨⟨0, by omega, 0, by omega, ?_⟩, by simp; omega⟩
    cases h : σ.childPositions with
    | nil => rw [h] at hp₀; simp at hp₀
    | cons x xs => rw [h] at hp₀; simp at hp₀; simp [hp₀]
  -- the recursion is a maximum over a nonempty list; take the cut attaining it
  have hnruns : ¬ σ.numRuns ≤ 1 := by omega
  unfold bound
  rw [boundFuel.eq_2, if_neg hnruns]
  dsimp only
  have hne : (σ.blocks.flatMap fun block =>
      (List.range (σ.k - 2)).flatMap fun d' =>
        [boundFuel σ.childPositions.length (σ.part block Side.lower (d' + 1)) +
            boundFuel σ.childPositions.length (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Side.upper (σ.k - 1 - (d' + 1))),
          boundFuel σ.childPositions.length (σ.part block Side.upper (σ.k - 1 - (d' + 1))) +
            boundFuel σ.childPositions.length (σ.part (σ.childPositions.filter (fun p => p ∉ block)) Side.lower (d' + 1))]) ≠ [] := by
    refine List.ne_nil_of_mem (List.mem_flatMap.2 ⟨[p₀], hb₀, List.mem_flatMap.2 ⟨0, ?_, List.mem_cons_self ..⟩⟩)
    exact List.mem_range.2 (by omega)
  obtain ⟨x, hx, hmax⟩ := exists_mem_eq_getD_max? _ hne
  rw [hmax]
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨block, hb, d', hd', hx⟩ := hx
  have hfB : ∀ s m, (σ.part block s m).childPositions.length + 1 ≤ σ.childPositions.length :=
    fun s m => part_childPositions_length_lt_of_mem_blocks hb s m
  have hfR : ∀ s m, (σ.part (σ.childPositions.filter (fun p => p ∉ block)) s m).childPositions.length + 1 ≤
      σ.childPositions.length :=
    fun s m => part_rest_childPositions_length_lt_of_mem_blocks hb s m
  have hdd : d' + 1 ≤ σ.k - 2 := by omega
  refine ctx_cut_le_end_cut σ hwf hruns block hb (d' + 1) (by omega) hdd x ?_
  rcases hx with rfl | rfl
  · left
    rw [boundFuel_eq_bound _ (hfB _ _), boundFuel_eq_bound _ (hfR _ _)]
  · right
    rw [boundFuel_eq_bound _ (hfB _ _), boundFuel_eq_bound _ (hfR _ _)]

end ErdosSzekeres
