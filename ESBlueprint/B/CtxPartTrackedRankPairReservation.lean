import ESBlueprint.B.CtxPartTrackedRankReservation

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Distinct endpoint-pair reservations for arbitrary removed source-active children, with tracked active supports and arbitrary positive indexed history. The pair potential is the union of all ordered pairs lying in one active child's available pure-rank interval on a selected axis. Every removed witness reserves its lower/upper endpoint pair: retained children on its right exclude the lower endpoint, and retained children on its left exclude the upper endpoint. All distinct reserved pairs lie in the source pair union and are absent from the part pair union, yielding the corresponding cardinal decrease and strict decrease for any nonempty removed witness set. Unlike individual-rank reservations, no common left/right orientation is needed, so this covers retained children straddling a removed witness. Supplies a concrete missing measure for the prospective quadratic higher-capacity potential; does not assert that the pair potential already bounds the full recursion.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_part_tracked_rank_pair_reservation (σ : Ctx.Context)
  (hpositive : ∀ p j v, σ.letterAt p = Ctx.Letter.ext j v → 1 ≤ j)
  (s : Ctx.Side) (keep : List ℕ) (m : ℕ) (F Q P : Finset ℕ)
  (hF : ∀ p ∈ F, p ∈ σ.childPositions ∧ 0 < σ.cupLimit p p ∧ 0 < σ.capLimit p p)
  (hQ : ∀ q ∈ Q, q ∈ (σ.part keep s m).childPositions ∧
    0 < (σ.part keep s m).cupLimit q q ∧ 0 < (σ.part keep s m).capLimit q q)
  (hQF : Q ⊆ F) (hP : ∀ p ∈ P, p ∈ F ∧ p ∉ keep) :
  let global := fun (ρ : Ctx.Context) (v : Ctx.Side) =>
    match v with | Ctx.Side.lower => ρ.u | Ctx.Side.upper => ρ.a
  let interval := fun (ρ : Ctx.Context) (p : ℕ) =>
    Finset.Icc (ρ.leftExt s 0 p + 1) (global ρ s - 1 - ρ.rightExt s 0 p)
  let pairs := fun (ρ : Ctx.Context) (p : ℕ) =>
    ((interval ρ p).product (interval ρ p)).filter (fun z => z.1 ≤ z.2)
  let sourcePairs := F.biUnion (pairs σ)
  let partPairs := Q.biUnion (pairs (σ.part keep s m))
  let reserved := P.image (fun p =>
    (σ.leftExt s 0 p + 1, global σ s - 1 - σ.rightExt s 0 p))
  reserved ⊆ sourcePairs ∧ partPairs ⊆ sourcePairs \ reserved ∧
    partPairs.card + reserved.card ≤ sourcePairs.card ∧
    (P.Nonempty → partPairs.card < sourcePairs.card) := by
  classical
  let G (ρ : Context) (v : Side) := match v with | Side.lower => ρ.u | Side.upper => ρ.a
  let I (ρ : Context) (p : ℕ) :=
    Finset.Icc (ρ.leftExt s 0 p + 1) (G ρ s - 1 - ρ.rightExt s 0 p)
  let Tri (ρ : Context) (p : ℕ) := ((I ρ p).product (I ρ p)).filter (fun z => z.1 ≤ z.2)
  let τ := σ.part keep s m
  let S := F.biUnion (Tri σ)
  let T := Q.biUnion (Tri τ)
  let E := P.image (fun p => (σ.leftExt s 0 p + 1, G σ s - 1 - σ.rightExt s 0 p))
  change E ⊆ S ∧ T ⊆ S \ E ∧ T.card + E.card ≤ S.card ∧ (P.Nonempty → T.card < S.card)
  have hTri (ρ : Context) (p : ℕ) (z : ℕ × ℕ) :
      z ∈ Tri ρ p ↔ z.1 ∈ I ρ p ∧ z.2 ∈ I ρ p ∧ z.1 ≤ z.2 := by
    simp [Tri, and_assoc]
  have hWidth (ρ : Context) (p : ℕ)
      (hc : 0 < ρ.cupLimit p p) (ha : 0 < ρ.capLimit p p) :
      ρ.leftExt s 0 p + 1 ≤ G ρ s - 1 - ρ.rightExt s 0 p := by
    cases s <;> simp only [G, cupLimit, capLimit, chainExt] at hc ha ⊢ <;> omega
  have hKeep (q : ℕ) (hq : q ∈ Q) : q ∈ keep := by
    have hh := (hQ q hq).1
    simp only [part_childPositions, List.mem_filter, decide_eq_true_eq] at hh
    exact hh.2
  have hI (q : ℕ) (hq : q ∈ Q) : I τ q ⊆ I σ q := by
    have hh := ctx_part_tracked_rank_reservation σ hpositive s keep m {q} {q} ∅ ∅
      (by intro r hr; simpa only [Finset.mem_singleton.mp hr] using hF q (hQF hq))
      (by intro r hr; simpa only [Finset.mem_singleton.mp hr] using hQ q hq)
      (by intro r hr; exact hr)
      (by simp) (by simp) (by simp) (by simp)
    simpa only [Finset.singleton_biUnion, Finset.image_empty, Finset.empty_union,
      Finset.sdiff_empty] using hh.2.1
  have hTS : T ⊆ S := by
    intro z hz
    obtain ⟨q, hq, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hza, hzb, hzab⟩ := (hTri τ q z).mp hz
    exact Finset.mem_biUnion.mpr ⟨q, hQF hq,
      (hTri σ q z).mpr ⟨hI q hq hza, hI q hq hzb, hzab⟩⟩
  have hES : E ⊆ S := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    have hpf := (hP p hp).1
    have hw := hWidth σ p (hF p hpf).2.1 (hF p hpf).2.2
    refine Finset.mem_biUnion.mpr ⟨p, hpf, (hTri σ p _).mpr ?_⟩
    exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, hw⟩,
      Finset.mem_Icc.mpr ⟨hw, le_rfl⟩, hw⟩
  have hExclude (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ Q) :
      (σ.leftExt s 0 p + 1, G σ s - 1 - σ.rightExt s 0 p) ∉ Tri τ q := by
    intro hz
    obtain ⟨hza, hzb, _⟩ := (hTri τ q _).mp hz
    have hpF := (hP p hp).1
    have hpnot := (hP p hp).2
    have hpq : p ≠ q := by
      intro he
      apply hpnot
      simpa only [he] using hKeep q hq
    have hF' : ∀ r ∈ ({p, q} : Finset ℕ),
        r ∈ σ.childPositions ∧ 0 < σ.cupLimit r r ∧ 0 < σ.capLimit r r := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with he | he
      · simpa only [he] using hF p hpF
      · simpa only [he] using hF q (hQF hq)
    have hQ' : ∀ r ∈ ({q} : Finset ℕ), r ∈ τ.childPositions ∧
        0 < τ.cupLimit r r ∧ 0 < τ.capLimit r r := by
      intro r hr
      simpa only [Finset.mem_singleton.mp hr] using hQ q hq
    have hQF' : ({q} : Finset ℕ) ⊆ {p, q} := by simp
    have hP' : ∀ r ∈ ({p} : Finset ℕ), r ∈ ({p, q} : Finset ℕ) ∧ r ∉ keep := by
      intro r hr
      have he := Finset.mem_singleton.mp hr
      subst r
      exact ⟨by simp, hpnot⟩
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · have hh := ctx_part_tracked_rank_reservation σ hpositive s keep m {p, q} {q} {p} ∅
        hF' hQ' hQF' hP' (by simp)
        (by intro a ha b hb; simpa only [Finset.mem_singleton.mp ha,
          Finset.mem_singleton.mp hb] using hlt) (by simp)
      have hex := hh.2.1
      simp only [Finset.singleton_biUnion, Finset.image_singleton, Finset.image_empty,
        Finset.union_empty] at hex
      exact (Finset.mem_sdiff.mp (hex hza)).2 (Finset.mem_singleton.mpr rfl)
    · have hh := ctx_part_tracked_rank_reservation σ hpositive s keep m {p, q} {q} ∅ {p}
        hF' hQ' hQF' (by simp) hP' (by simp)
        (by intro a ha b hb; simpa only [Finset.mem_singleton.mp ha,
          Finset.mem_singleton.mp hb] using hgt)
      have hex := hh.2.1
      simp only [Finset.singleton_biUnion, Finset.image_empty, Finset.image_singleton,
        Finset.empty_union] at hex
      exact (Finset.mem_sdiff.mp (hex hzb)).2 (Finset.mem_singleton.mpr rfl)
  have hTE : Disjoint T E := by
    apply Finset.disjoint_left.mpr
    intro z hz he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q, hq, hz⟩ := Finset.mem_biUnion.mp hz
    exact hExclude p hp q hq hz
  have hsub : T ⊆ S \ E := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hTS hz, fun he => Finset.disjoint_left.mp hTE hz he⟩
  have hcard : T.card + E.card ≤ S.card := by
    have hh := Finset.card_le_card (Finset.union_subset hTS hES)
    rw [Finset.card_union_of_disjoint hTE] at hh
    exact hh
  refine ⟨hES, hsub, hcard, ?_⟩
  intro hnonempty
  have he : E.Nonempty := hnonempty.image _
  have hpos := Finset.card_pos.mpr he
  omega

end ErdosSzekeres
