import ESBlueprint.B.CtxTwoMarkerEndpointCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerInternalIntervalCutPotentialBound
import ESBlueprint.B.CtxTwoMarkerInternalComplementCutObstructionClassification
import ESBlueprint.B.CtxBaseCrossAxisTransfer
import ESBlueprint.B.CtxBoundAttainedByEndCut
import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- All endpoint cuts, chosen internal intervals and the other opposite-kept internal geometries satisfy P(w). A direct unfolding of the literal recurrence reduces the full potential to the older-exterior opposite-kept cut family at the same source, with legal positive maxima m+n=k-1. No smaller-width recursive premise is used.
Positive labels, chosen global at most five, opposite width at least two, two actual chosen positions at N<M containing all indexed chosen positions, and no indexed opposite history. Explicit remaining hypothesis: every legal older-exterior opposite-kept internal block cut at this source satisfies P(w). This cut family is not proved by the reduction. Source maxima and inactive children are arbitrary; no smaller-width recursive potential assumption.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_potential_of_older_exterior_cut_bound (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ)
  (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M)
  (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s)
  (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M)
  (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5)
  (hclear : σ.levelsOn t 0 = [])
  (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y)
  (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1)
  (hExterior : ∀ (keep : List ℕ), keep ∈ σ.blocks →
    ∀ (q₀ l r m n : ℕ), q₀ ∈ keep →
    l ∈ σ.childPositions → r ∈ σ.childPositions → l ∉ keep → r ∉ keep →
    (∀ p ∈ keep, l < p ∧ p < r) →
    ((x < y ∧ ∀ p ∈ keep, y < p) ∨ (y < x ∧ ∀ p ∈ keep, p < y)) →
    1 ≤ m → 1 ≤ n → m + n = σ.k - 1 →
    let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
    (σ.part (σ.childPositions.filter (· ∉ keep)) s m).bound +
      (σ.part keep t n).bound ≤ (w + 1).choose 2 + w - 1) :
  let w := (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1
  (∀ fuel, Ctx.Context.boundFuel fuel σ ≤ (w + 1).choose 2 + w - 1) ∧
    σ.bound ≤ (w + 1).choose 2 + w - 1 := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let C (ρ : Context) (v : Side) (p : ℕ) := match v with
    | Side.lower => ρ.cupLimit p p | Side.upper => ρ.capLimit p p
  let w := G σ t - 1
  let P := (w + 1).choose 2 + w - 1
  let Convex (ρ : Context) (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
    ∀ z ∈ ρ.childPositions, a ≤ z → z ≤ b → z ∈ ks
  change (∀ fuel, boundFuel fuel σ ≤ P) ∧ σ.bound ≤ P
  have hw : 2 ≤ w := hwidth
  have hNOn : N ∈ σ.levelsOn s 0 := List.mem_filter.mpr ⟨hN, by simp [hNs]⟩
  have hOneLeft (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hqp : q < p) :
      1 ≤ ρ.leftExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (· < p) := by simp [hq, hqp]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (leftStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.leftExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, leftStep,
      List.getLast?_eq_some_getLast hnonempty] using hv
  have hOneRight (ρ : Context) (v : Side) (j p q : ℕ)
      (hj : j ∈ ρ.levelsOn v 0) (hq : q ∈ ρ.extPositions j) (hpq : p < q) :
      1 ≤ ρ.rightExt v 0 p := by
    have hm : q ∈ (ρ.extPositions j).filter (p < ·) := by simp [hq, hpq]
    have hnonempty := List.ne_nil_of_mem hm
    have hv := le_getD_max?_of_mem (L := (ρ.levelsOn v 0).sublists.map
      (fun ls => (ls.foldl (rightStep ρ) (p, 0)).2))
      (List.mem_map.mpr ⟨[j], List.mem_sublists.mpr (List.singleton_sublist.mpr hj), rfl⟩)
    change _ ≤ ρ.rightExt v 0 p at hv
    simpa only [List.foldl_cons, List.foldl_nil, rightStep,
      List.head?_eq_some_head hnonempty] using hv
  have hBaseThree (p k : ℕ) (hp : p ≤ k - 1) : baseOf 3 p k ≤ (p + 1).choose 2 := by
    by_cases hp0 : p = 0
    · subst p
      simp [baseOf]
    by_cases hp1 : p = 1
    · subst p
      norm_num [baseOf]
    have hp2 : 2 ≤ p := by omega
    simp only [baseOf, if_neg (show ¬(3 = 0 ∨ p = 0) by omega),
      if_neg (show ¬(3 = 1 ∨ p = 1) by omega)]
    by_cases hpk : p + 2 ≤ k
    · rw [decomposableThreshold_eq_choose (by omega) (by omega) (by omega)]
      have hrow : p + 1 + (3 + 1) - 4 = p + 1 := by omega
      have hcol : p + 1 - 2 = (p + 1) - 2 := rfl
      rw [hrow]
      exact (Nat.choose_symm (show 2 ≤ p + 1 by omega)).le
    · have hk : k = p + 1 := by omega
      subst k
      rw [decomposableThreshold_eq_window (by omega) (by omega) (by omega)]
      have hwindow : decomposableBinomialWindow (p + 1) (3 + 1) (p + 1) =
          1 + (p - 1) + (p - 1).choose 2 := by
        have hr : p + 1 - 2 = p - 1 := by omega
        norm_num [decomposableBinomialWindow, hr, Finset.sum_Icc_succ_top]
      rw [hwindow]
      have hp' : p = (p - 1) + 1 := by omega
      have hpascal : (p + 1).choose 2 = (p - 1).choose 2 + (p - 1) + p := by
        calc
          (p + 1).choose 2 = p + p.choose 2 := by simp [Nat.choose_succ_succ']
          _ = (p - 1).choose 2 + (p - 1) + p := by
            conv_lhs => arg 2; rw [hp']
            simp [Nat.choose_succ_succ']
            omega
      omega
  have hBaseLower (c p k : ℕ) (hc : c ≤ 3) (hp : p ≤ k - 1) :
      baseOf c p k ≤ (p + 1).choose 2 :=
    (baseOf_mono hc le_rfl).trans (hBaseThree p k hp)
  have hBaseSwap (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      baseOf x y k = baseOf y x k := by
    have hz (r : ℕ) : baseOf 0 r k = 0 := by simp [baseOf]
    have hz' (r : ℕ) : baseOf r 0 k = 0 := by simp [baseOf]
    apply Nat.le_antisymm
    · have hh := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
    · have hh := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by omega)
      simpa only [Nat.zero_add, hz, hz', Nat.add_zero] using hh
  have hBaseUpper (c p k : ℕ) (hp : p ≤ 3) (hc : c ≤ k - 1) (hpk : p ≤ k - 1) :
      baseOf c p k ≤ (c + 1).choose 2 := by
    rw [hBaseSwap c p k hc hpk]
    exact hBaseLower p c k hp hc
  have hBlockConvex (ρ : Context) (ks : List ℕ) (hk : ks ∈ ρ.blocks) : Convex ρ ks := by
    obtain ⟨i, l, _, _, hwindow⟩ := exists_take_drop_of_mem_blocks hk
    have hinfix : ks <:+: ρ.childPositions := by
      refine ⟨ρ.childPositions.take i, (ρ.childPositions.drop i).drop (l+1), ?_⟩
      rw [hwindow, List.append_assoc, List.take_append_drop, List.take_append_drop]
    obtain ⟨pre, post, he⟩ := hinfix
    have he' : pre ++ (ks ++ post) = ρ.childPositions := by simpa only [List.append_assoc] using he
    have hs : (pre ++ (ks ++ post)).Pairwise (· < ·) := by
      rw [he']
      exact childPositions_pairwise ρ
    have hbefore : ∀ a ∈ pre, ∀ b ∈ ks, a < b := by
      intro a ha b hb
      exact (List.pairwise_append.mp hs).2.2 a ha b (List.mem_append_left post hb)
    have hafter : ∀ a ∈ ks, ∀ b ∈ post, a < b :=
      (List.pairwise_append.mp (List.pairwise_append.mp hs).2.1).2.2
    intro a ha b hb z hz haz hzb
    rw [← he'] at hz
    rcases List.mem_append.mp hz with hz | hz
    · have hh := hbefore z hz a ha
      omega
    · rcases List.mem_append.mp hz with hz | hz
      · exact hz
      · have hh := hafter b hb z hz
        omega
  have hNe (p : ℕ) (hp : p ∈ σ.childPositions) : p ≠ x := by
    intro he
    subst p
    have hc := of_decide_eq_true (List.mem_filter.mp hp).2
    have he := (List.mem_filter.mp hx).2
    simp [hc] at he
  have hSmallChosen (p : ℕ) (hp : p ∈ σ.childPositions) : C σ s p ≤ 3 := by
    have hn := hNe p hp
    by_cases hpx : p < x
    · have he := hOneRight σ s N p x hNOn hx hpx
      cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
    · have he := hOneLeft σ s N p x hNOn hx (by omega)
      cases s <;> simp only [C, cupLimit, capLimit, chainExt] at hglobal ⊢ <;> omega
  have hOppCap (p : ℕ) : C σ t p ≤ w := by
    cases t <;> simp only [C, w, G, cupLimit, capLimit] <;> omega
  have hTriangle : (w + 1).choose 2 ≤ P := by dsimp only [P]; omega
  have hBase : σ.base ≤ P := by
    rw [base_eq_baseOf]
    cases he : σ.childPositions.head? with
    | none => exact Nat.zero_le _
    | some p =>
      have hp := List.mem_of_mem_head? (Option.mem_def.mpr he)
      have hc := hSmallChosen p hp
      have hcupk : σ.cupLimit p p ≤ σ.k - 1 := by dsimp only [cupLimit]; omega
      have hcapk : σ.capLimit p p ≤ σ.k - 1 := by dsimp only [capLimit]; omega
      have hleaf : baseOf (σ.cupLimit p p) (σ.capLimit p p) σ.k ≤ (C σ t p + 1).choose 2 := by
        cases s <;> cases t
        · exact False.elim (hne rfl)
        · exact hBaseLower _ _ _ hc hcapk
        · exact hBaseUpper _ _ _ hc hcupk hcapk
        · exact False.elim (hne rfl)
      exact hleaf.trans ((Nat.choose_le_choose 2 (Nat.add_le_add_right (hOppCap p) 1)).trans hTriangle)
  have hFuelFull (ρ : Context) (f : ℕ) : boundFuel f ρ ≤ ρ.bound := by
    by_cases hf : ρ.childPositions.length + 1 ≤ f
    · exact (boundFuel_eq_bound ρ hf).le
    · exact boundFuel_mono (by omega : f ≤ ρ.childPositions.length + 1) ρ
  have hCut (keep : List ℕ) (hk : keep ∈ σ.blocks) (m n f g : ℕ)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsum : m + n = σ.k - 1) :
      (boundFuel f (σ.part keep s m) +
        boundFuel g (σ.part (σ.childPositions.filter (· ∉ keep)) t n) ≤ P) ∧
      (boundFuel f (σ.part (σ.childPositions.filter (· ∉ keep)) s m) +
        boundFuel g (σ.part keep t n) ≤ P) := by
    obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hk
    obtain ⟨q₀, hq₀⟩ := List.exists_mem_of_ne_nil _ hkne
    have hremoved : ∃ q ∈ σ.childPositions, q ∉ keep := by
      by_contra h
      push Not at h
      have hlen := ((childPositions_nodup σ).subperm h).length_le
      omega
    obtain ⟨r₀, hr₀, hrnot⟩ := hremoved
    let rest := σ.childPositions.filter (· ∉ keep)
    have hrest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by simp [rest]
    have hrrest : r₀ ∈ rest := (hrest r₀).mpr ⟨hr₀, hrnot⟩
    have hqnot : q₀ ∉ rest := by simp [rest, hq₀]
    have hconv := hBlockConvex σ keep hk
    have hOutside (p : ℕ) (hp : p ∈ rest) :
        (∀ q ∈ keep, p < q) ∨ (∀ q ∈ keep, q < p) := by
      have hpc := (hrest p).mp hp
      by_cases hpq : p < q₀
      · left
        intro q hq
        by_contra hbad
        exact hpc.2 (hconv q hq q₀ hq₀ p hpc.1 (by omega) (by omega))
      · right
        intro q hq
        by_contra hbad
        exact hpc.2 (hconv q₀ hq₀ q hq p hpc.1 (by omega) (by omega))
    have hEnd (direction : Bool)
        (he : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
          if direction then p < q else q < p) :
        (boundFuel f (σ.part keep s m) + boundFuel g (σ.part rest t n) ≤ P) ∧
        (boundFuel f (σ.part rest s m) + boundFuel g (σ.part keep t n) ≤ P) := by
      have heOpp : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
          if !direction then q < p else p < q := by
        intro p hp q hq hqn
        have hh := he p hp q hq hqn
        cases direction <;> simpa using hh
      have hbackward := ctx_two_marker_endpoint_cut_potential_bound σ hpositive s t hne
        N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
        keep q₀ r₀ m n hq₀ hksub hr₀ hrnot (!direction) heOpp
      have heRest : ∀ p ∈ rest, ∀ q ∈ σ.childPositions, q ∉ rest →
          if direction then q < p else p < q := by
        intro p hp q hq hqn
        have hpk := (hrest p).mp hp
        have hqk : q ∈ keep := by simpa [rest, hq] using hqn
        have hh := he q hqk p hpk.1 hpk.2
        cases direction <;> simpa using hh
      have hforward := ctx_two_marker_endpoint_cut_potential_bound σ hpositive s t hne
        N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
        rest r₀ q₀ m n hrrest (fun p hp => ((hrest p).mp hp).1)
        (hksub q₀ hq₀) hqnot direction heRest
      have hdouble : σ.part (σ.childPositions.filter (· ∉ rest)) s m = σ.part keep s m := by
        apply part_congr
        intro p hp
        simp [rest, hp]
      exact ⟨by simpa only [hdouble] using hforward.1 f g, hbackward.1 f g⟩
    by_cases hL : ∃ l ∈ rest, ∀ p ∈ keep, l < p
    · obtain ⟨l, hlrest, hlbefore⟩ := hL
      by_cases hR : ∃ r ∈ rest, ∀ p ∈ keep, p < r
      · obtain ⟨r, hrrest, hrafter⟩ := hR
        have hl := (hrest l).mp hlrest
        have hr := (hrest r).mp hrrest
        have hinside : ∀ p ∈ keep, l < p ∧ p < r := fun p hp => ⟨hlbefore p hp, hrafter p hp⟩
        have hforward := ctx_two_marker_internal_interval_cut_potential_bound σ hpositive s t hne
          N M x y hN hM hNM hNs hMs hx hy hglobal hchosen hwidth
          keep q₀ l r m n hq₀ hksub hl.1 hr.1 hl.2 hr.2 hinside hconv
        refine ⟨hforward.1 f g, ?_⟩
        have hclass := ctx_two_marker_internal_complement_cut_obstruction_classification σ hpositive
          s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hclear hchosen hwidth
          keep q₀ l r m n hq₀ hksub hl.1 hr.1 hl.2 hr.2 hinside hconv
        rcases hclass with hbound | hgeom
        · exact hbound.1 f g
        · exact (Nat.add_le_add (hFuelFull _ f) (hFuelFull _ g)).trans
            (hExterior keep hk q₀ l r m n hq₀ hl.1 hr.1 hl.2 hr.2 hinside hgeom hm hn hsum)
      · apply hEnd false
        intro p hp q hq hqnot
        have hqr : q ∈ rest := (hrest q).mpr ⟨hq, hqnot⟩
        rcases hOutside q hqr with hh | hh
        · exact hh p hp
        · exact False.elim (hR ⟨q, hqr, hh⟩)
    · apply hEnd true
      intro p hp q hq hqnot
      have hqr : q ∈ rest := (hrest q).mpr ⟨hq, hqnot⟩
      rcases hOutside q hqr with hh | hh
      · exact False.elim (hL ⟨q, hqr, hh⟩)
      · exact hh p hp
  have hFuel (fuel : ℕ) : boundFuel fuel σ ≤ P := by
    cases fuel with
    | zero => exact Nat.zero_le _
    | succ fuel =>
      rw [boundFuel]
      split
      · exact hBase
      · apply Ctx.getD_max?_le
        intro z hz
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hz
        obtain ⟨keep, hkeep, d, hd, hz⟩ := hz
        let rest := σ.childPositions.filter (· ∉ keep)
        have hforward (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = σ.k - 1) :
            boundFuel fuel (σ.part keep s a) + boundFuel fuel (σ.part rest t b) ≤ P :=
          (hCut keep hkeep a b fuel fuel ha hb hab).1
        have hbackward (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = σ.k - 1) :
            boundFuel fuel (σ.part rest s a) + boundFuel fuel (σ.part keep t b) ≤ P :=
          (hCut keep hkeep a b fuel fuel ha hb hab).2
        have hboth (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a + b = σ.k - 1) :
            (boundFuel fuel (σ.part keep Side.lower a) +
              boundFuel fuel (σ.part rest Side.upper b) ≤ P) ∧
            (boundFuel fuel (σ.part keep Side.upper b) +
              boundFuel fuel (σ.part rest Side.lower a) ≤ P) := by
          cases s <;> cases t
          · exact False.elim (hne rfl)
          · exact ⟨hforward a b ha hb hab, by simpa only [Nat.add_comm] using hbackward a b ha hb hab⟩
          · exact ⟨by simpa only [Nat.add_comm] using hbackward b a hb ha (by omega),
              hforward b a hb ha (by omega)⟩
          · exact False.elim (hne rfl)
        rcases hz with rfl | rfl
        · exact (hboth (d + 1) (σ.k - 1 - (d + 1)) (by omega) (by omega) (by omega)).1
        · exact (hboth (d + 1) (σ.k - 1 - (d + 1)) (by omega) (by omega) (by omega)).2
  exact ⟨hFuel, hFuel (σ.childPositions.length + 1)⟩

end ErdosSzekeres
