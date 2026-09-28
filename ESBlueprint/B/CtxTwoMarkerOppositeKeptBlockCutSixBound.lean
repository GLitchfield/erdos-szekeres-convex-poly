import ESBlueprint.B.CtxTwoMarkerEndpointCutSixBound
import ESBlueprint.B.CtxTwoMarkerInternalComplementCutSixBound

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Every opposite-kept recurrence block cut in a two-marker k-six context has independently fueled and full sums at most twelve. Block geometry supplies either an endpoint ordering or complementary witnesses bracketing a convex internal interval, so the checked endpoint and internal-complement theorems cover all cases.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_two_marker_endpoint_cut_six_bound, ErdosSzekeres.ctx_two_marker_internal_complement_cut_six_bound
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_two_marker_opposite_kept_block_cut_six_bound (σ : Ctx.Context) (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j) (s t : Ctx.Side) (hne : s ≠ t) (N M x y : ℕ) (hN : N ∈ σ.levels) (hM : M ∈ σ.levels) (hNM : N < M) (hNs : σ.sideAt N = s) (hMs : σ.sideAt M = s) (hx : x ∈ σ.extPositions N) (hy : y ∈ σ.extPositions M) (hglobal : (match s with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hopposite : (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) ≤ 5) (hclear : σ.levelsOn t 0 = []) (hchosen : ∀ j ∈ σ.levelsOn s 0, ∀ p ∈ σ.extPositions j, p = x ∨ p = y) (hwidth : 2 ≤ (match t with | Ctx.Side.lower => σ.u | Ctx.Side.upper => σ.a) - 1) (keep : List ℕ) (hblock : keep ∈ σ.blocks) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcoupling : m + n = σ.k - 1) (hk : σ.k = 6) : let rest := σ.childPositions.filter (· ∉ keep); (∀ f g, Ctx.Context.boundFuel f (σ.part rest s m) + Ctx.Context.boundFuel g (σ.part keep t n) ≤ 12) ∧ (σ.part rest s m).bound + (σ.part keep t n).bound ≤ 12 := by
  classical
  let Convex (ks : List ℕ) := ∀ a ∈ ks, ∀ b ∈ ks,
    ∀ z ∈ σ.childPositions, a ≤ z → z ≤ b → z ∈ ks
  have hBlockConvex (ks : List ℕ) (hks : ks ∈ σ.blocks) : Convex ks := by
    obtain ⟨i, l, _, _, hwindow⟩ := exists_take_drop_of_mem_blocks hks
    have hinfix : ks <:+: σ.childPositions := by
      refine ⟨σ.childPositions.take i, (σ.childPositions.drop i).drop (l + 1), ?_⟩
      rw [hwindow, List.append_assoc, List.take_append_drop, List.take_append_drop]
    obtain ⟨pre, post, he⟩ := hinfix
    have he' : pre ++ (ks ++ post) = σ.childPositions := by
      simpa only [List.append_assoc] using he
    have hs : (pre ++ (ks ++ post)).Pairwise (· < ·) := by
      rw [he']
      exact childPositions_pairwise σ
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
  obtain ⟨hkl, hkne, hksub⟩ := mem_blocks hblock
  obtain ⟨q₀, hq₀⟩ := List.exists_mem_of_ne_nil _ hkne
  have hremoved : ∃ q ∈ σ.childPositions, q ∉ keep := by
    by_contra h
    push Not at h
    have hlen := ((childPositions_nodup σ).subperm h).length_le
    omega
  obtain ⟨r₀, hr₀, hr₀not⟩ := hremoved
  let rest := σ.childPositions.filter (· ∉ keep)
  have hrest (p : ℕ) : p ∈ rest ↔ p ∈ σ.childPositions ∧ p ∉ keep := by
    simp [rest]
  have hconvex := hBlockConvex keep hblock
  have hOutside (p : ℕ) (hp : p ∈ rest) :
      (∀ q ∈ keep, p < q) ∨ (∀ q ∈ keep, q < p) := by
    have hpc := (hrest p).mp hp
    by_cases hpq : p < q₀
    · left
      intro q hq
      by_contra hbad
      exact hpc.2 (hconvex q hq q₀ hq₀ p hpc.1 (by omega) (by omega))
    · right
      intro q hq
      by_contra hbad
      exact hpc.2 (hconvex q₀ hq₀ q hq p hpc.1 (by omega) (by omega))
  by_cases hL : ∃ l ∈ rest, ∀ p ∈ keep, l < p
  · obtain ⟨l, hlrest, hlbefore⟩ := hL
    by_cases hR : ∃ r ∈ rest, ∀ p ∈ keep, p < r
    · obtain ⟨r, hrrest, hrafter⟩ := hR
      have hl := (hrest l).mp hlrest
      have hr := (hrest r).mp hrrest
      have hinside : ∀ p ∈ keep, l < p ∧ p < r :=
        fun p hp => ⟨hlbefore p hp, hrafter p hp⟩
      have hh := ctx_two_marker_internal_complement_cut_six_bound σ hpositive
        s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite hclear hchosen
        hwidth keep q₀ l r m n hq₀ hksub hl.1 hr.1 hl.2 hr.2 hinside hconvex
        hk hm hn hcoupling
      simpa only [rest] using hh
    · have hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
          if true then q < p else p < q := by
        intro p hp q hq hqnot
        have hqr : q ∈ rest := (hrest q).mpr ⟨hq, hqnot⟩
        rcases hOutside q hqr with hh | hh
        · exact hh p hp
        · exact False.elim (hR ⟨q, hqr, hh⟩)
      have hh := ctx_two_marker_endpoint_cut_six_bound σ hpositive
        s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite hclear hchosen
        hwidth keep q₀ r₀ m n hq₀ hksub hr₀ hr₀not true hendpoint
        hk hm hn hcoupling
      simpa only [rest] using hh
  · have hendpoint : ∀ p ∈ keep, ∀ q ∈ σ.childPositions, q ∉ keep →
        if false then q < p else p < q := by
      intro p hp q hq hqnot
      have hqr : q ∈ rest := (hrest q).mpr ⟨hq, hqnot⟩
      rcases hOutside q hqr with hh | hh
      · exact False.elim (hL ⟨q, hqr, hh⟩)
      · exact hh p hp
    have hh := ctx_two_marker_endpoint_cut_six_bound σ hpositive
      s t hne N M x y hN hM hNM hNs hMs hx hy hglobal hopposite hclear hchosen
      hwidth keep q₀ r₀ m n hq₀ hksub hr₀ hr₀not false hendpoint
      hk hm hn hcoupling
    simpa only [rest] using hh

end ErdosSzekeres
