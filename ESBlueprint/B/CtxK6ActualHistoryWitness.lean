import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import Mathlib.Data.Fintype.Powerset

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace ErdosSzekeres

/-- Exact actual seven-vertex history for the R19 k6 context SSS1L3L2LS/maxima111 at(5,5,6): explicit largest-external-level coloring is decomposable and sweep-realizable, three nested lower-child/upper-singleton splits have actual sibling cap maxima1, the root avoids5-cap/5-cup/strong6, three root parts give the literal context, and the actual four-child subset satisfies it. This certifies feasibility of the cost/end-selection example without claiming sharp child cardinality8, general feasible PEEL, or the stronger coordinate deep-below predicate for this tree.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_satisfies_of_deepBelowSplit
@dangling-ok R19 exact scope verification: removes actual external-history uncertainty for the certified k6 end/cost example; forced singleton-ancestor tree admits finite proof and closed context transfer. -/
theorem ctx_k6_actual_history_witness : let level : Fin 7 → ℕ := fun v =>
    if v = 3 then 1 else if v = 4 then 3 else if v = 5 then 2 else 0
  let χ : TripleColoring 7 := fun t =>
    let m := max (level t.i) (max (level t.j) (level t.k))
    if 0 < m ∧ level t.j ≠ m then Turn.left else Turn.right
  let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  IsDecomposable χ ∧ IsSweepRealizable χ ∧
  HasDeepBelowSplit χ {0, 1, 2, 3, 5, 6} {4} ∧
  HasDeepBelowSplit χ {0, 1, 2, 3, 6} {5} ∧
  HasDeepBelowSplit χ {0, 1, 2, 6} {3} ∧
  Ctx.chainMax χ {3} false = 1 ∧
  Ctx.chainMax χ {4} false = 1 ∧
  Ctx.chainMax χ {5} false = 1 ∧
  (∀ C : Finset (Fin 7),
    (IsCapSet χ C → C.card ≤ 4) ∧
    (IsCupSet χ C → C.card ≤ 4) ∧
    (IsStrongPolygonSet χ C → C.card ≤ 5)) ∧
  ((((Ctx.Context.root 5 5 6 7).part [0, 1, 2, 3, 5, 6] Ctx.Side.lower 1).part
      [0, 1, 2, 3, 6] Ctx.Side.lower 1).part [0, 1, 2, 6] Ctx.Side.lower 1 = σ) ∧
  Ctx.Satisfies χ {0, 1, 2, 6} σ := by
  dsimp only
  let level : Fin 7 → ℕ := fun v =>
    if v = 3 then 1 else if v = 4 then 3 else if v = 5 then 2 else 0
  let χ : TripleColoring 7 := fun t =>
    let m := max (level t.i) (max (level t.j) (level t.k))
    if 0 < m ∧ level t.j ≠ m then Turn.left else Turn.right
  let lower : Fin 6 → Finset (Fin 7) := fun r => match r.val with
    | 0 => {0, 1, 2, 3, 5, 6}
    | 1 => {0, 1, 2, 3, 6}
    | 2 => {0, 1, 2, 6}
    | 3 => {6}
    | 4 => {2}
    | _ => {1}
  let upper : Fin 6 → Finset (Fin 7) := fun r => match r.val with
    | 0 => {4}
    | 1 => {5}
    | 2 => {3}
    | 3 => {0, 1, 2}
    | 4 => {0, 1}
    | _ => {0}
  have hdisjoint : ∀ r : Fin 6, Disjoint (lower r) (upper r) := by
    decide +kernel
  have hcross : ∀ (r : Fin 6) (i j k : Fin 7) (hij : i < j) (hjk : j < k),
      i ∈ lower r ∪ upper r → j ∈ lower r ∪ upper r → k ∈ lower r ∪ upper r →
      ¬(i ∈ lower r ∧ j ∈ lower r ∧ k ∈ lower r) →
      ¬(i ∈ upper r ∧ j ∈ upper r ∧ k ∈ upper r) →
      χ ⟨i, j, k, hij, hjk⟩ = if j ∈ lower r then Turn.left else Turn.right := by
    decide +kernel
  have hdeep : ∀ r : Fin 6, HasDeepBelowSplit χ (lower r) (upper r) := by
    intro r
    exact ⟨hdisjoint r, fun t => hcross r t.i t.j t.k t.hij t.hjk⟩
  have hfinite : ∀ C : Finset (Fin 7),
      (C.card ≤ 4 ∨ ¬(∀ (i j k : Fin 7) (hij : i < j) (hjk : j < k),
        i ∈ C → j ∈ C → k ∈ C → χ ⟨i, j, k, hij, hjk⟩ = Turn.right)) ∧
      (C.card ≤ 4 ∨ ¬(∀ (i j k : Fin 7) (hij : i < j) (hjk : j < k),
        i ∈ C → j ∈ C → k ∈ C → χ ⟨i, j, k, hij, hjk⟩ = Turn.left)) ∧
      (C.card ≤ 5 ∨ ¬(∀ (i j k l : Fin 7) (hij : i < j) (hjk : j < k) (hkl : k < l),
        i ∈ C → j ∈ C → k ∈ C → l ∈ C →
        χ ⟨i, j, k, hij, hjk⟩ = χ ⟨i, j, l, hij, hjk.trans hkl⟩ ∧
        χ ⟨i, k, l, hij.trans hjk, hkl⟩ = χ ⟨j, k, l, hjk, hkl⟩)) := by
    dsimp only [χ, level]
    set_option synthInstance.maxSize 512 in
      decide +kernel
  have hprofile : ∀ C : Finset (Fin 7),
      (IsCapSet χ C → C.card ≤ 4) ∧ (IsCupSet χ C → C.card ≤ 4) ∧
      (IsStrongPolygonSet χ C → C.card ≤ 5) := by
    intro C
    refine ⟨fun hc => (hfinite C).1.resolve_right (fun hn => hn ?_),
      fun hc => (hfinite C).2.1.resolve_right (fun hn => hn ?_),
      fun hc => (hfinite C).2.2.resolve_right (fun hn => hn ?_)⟩
    · intro i j k hij hjk hi hj hk
      exact hc ⟨i, j, k, hij, hjk⟩ hi hj hk
    · intro i j k hij hjk hi hj hk
      exact hc ⟨i, j, k, hij, hjk⟩ hi hj hk
    · intro i j k l hij hjk hkl hi hj hk hl
      exact hc hij hjk hkl hi hj hk hl
  have hd01 : IsDecomposableOn χ {0, 1} := by
    convert IsDecomposableOn.split (IsDecomposableOn.singleton 1)
      (IsDecomposableOn.singleton 0) (hdeep 5) using 1 <;> decide +kernel
  have hd012 : IsDecomposableOn χ {0, 1, 2} := by
    convert IsDecomposableOn.split (IsDecomposableOn.singleton 2) hd01
      (hdeep 4) using 1 <;> decide +kernel
  have hdcore : IsDecomposableOn χ (lower 2) := by
    convert IsDecomposableOn.split (IsDecomposableOn.singleton 6) hd012
      (hdeep 3) using 1 <;> decide +kernel
  have hd1 : IsDecomposableOn χ (lower 1) := by
    convert IsDecomposableOn.split hdcore (IsDecomposableOn.singleton 3)
      (hdeep 2) using 1 <;> decide +kernel
  have hd0 : IsDecomposableOn χ (lower 0) := by
    convert IsDecomposableOn.split hd1 (IsDecomposableOn.singleton 5)
      (hdeep 1) using 1 <;> decide +kernel
  have hdec : IsDecomposable χ := by
    unfold IsDecomposable
    convert IsDecomposableOn.split hd0 (IsDecomposableOn.singleton 4)
      (hdeep 0) using 1 <;> decide +kernel
  have hsingle (v : Fin 7) : Ctx.chainMax χ {v} false = 1 := by
    apply le_antisymm
    · apply Ctx.chainMax_le_iff.2
      intro C hC _
      simpa using Finset.card_le_card hC
    · exact Ctx.one_le_chainMax (Finset.singleton_nonempty v) false
  let θ0 := Ctx.Context.root 5 5 6 7
  let θ1 := θ0.part [0, 1, 2, 3, 5, 6] Ctx.Side.lower 1
  let θ2 := θ1.part [0, 1, 2, 3, 6] Ctx.Side.lower 1
  let θ3 := θ2.part [0, 1, 2, 6] Ctx.Side.lower 1
  let σ : Ctx.Context :=
    ⟨5, 5, 6,
      [Ctx.Letter.child, Ctx.Letter.child, Ctx.Letter.child,
       Ctx.Letter.ext 1 Ctx.Side.lower, Ctx.Letter.ext 3 Ctx.Side.lower,
       Ctx.Letter.ext 2 Ctx.Side.lower, Ctx.Letter.child], [1, 1, 1]⟩
  have hwf0 : θ0.WellFormed := by
    refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
    · simp [θ0, Ctx.Context.root]
    · intro p l s hp
      have hchild : θ0.letterAt p = Ctx.Letter.child := by
        change ((List.replicate 7 Ctx.Letter.child)[p]?).getD Ctx.Letter.child =
          Ctx.Letter.child
        rw [List.getElem?_replicate]
        split <;> rfl
      rw [hchild] at hp
      cases hp
  have hs0 : Ctx.Satisfies χ (Finset.univ : Finset (Fin 7)) θ0 := by
    refine ⟨by decide +kernel, ?_⟩
    intro C hC hne
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · change IsCupSet χ C → C.card ≤ 4
      exact (hprofile C).2.1
    · change IsCapSet χ C → C.card ≤ 4
      exact (hprofile C).1
    · change IsStrongPolygonSet χ C → C.card ≤ 5
      exact (hprofile C).2.2
  have hposEq (θ : Ctx.Context) (S T : Finset (Fin 7)) (keep : List ℕ)
      (hmap : ∀ v ∈ T, (θ.childPositions[(S.filter (· < v)).card]?).getD 0 = v.val)
      (hvalues : T.image Fin.val = keep.toFinset)
      (hsorted : keep.Pairwise (· ≤ ·)) (hnodup : keep.Nodup) :
      θ.positionsOf S T = keep := by
    have hps := Ctx.Context.positionsOf_pairwise_lt θ S T
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (hps.imp le_of_lt) hsorted
    apply (List.perm_ext_iff_of_nodup (hps.imp ne_of_lt) hnodup).2
    intro p
    rw [Ctx.Context.mem_positionsOf]
    have heq :
        (∃ v ∈ T, (θ.childPositions[(S.filter (· < v)).card]?).getD 0 = p) ↔
          (∃ v ∈ T, v.val = p) := by
      apply exists_congr
      intro v
      apply and_congr_right
      intro hv
      rw [hmap v hv]
    rw [heq, ← Finset.mem_image, hvalues, List.mem_toFinset]
  have hpos0 : θ0.positionsOf (Finset.univ : Finset (Fin 7)) (lower 0) =
      [0, 1, 2, 3, 5, 6] := by
    apply hposEq
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  have hpos1 : θ1.positionsOf (lower 0) (lower 1) = [0, 1, 2, 3, 6] := by
    apply hposEq
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  have hpos2 : θ2.positionsOf (lower 1) (lower 2) = [0, 1, 2, 6] := by
    apply hposEq
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
  have hmax0 : Ctx.chainMax χ (upper 0) false = 1 := hsingle 4
  have hmax1 : Ctx.chainMax χ (upper 1) false = 1 := hsingle 5
  have hmax2 : Ctx.chainMax χ (upper 2) false = 1 := hsingle 3
  have hs1 : Ctx.Satisfies χ (lower 0) θ1 := by
    have h := (ctx_satisfies_of_deepBelowSplit θ0 hwf0 hs0 (hdeep 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
    rw [hpos0, hmax0] at h
    exact h
  have hwf1 : θ1.WellFormed :=
    hwf0.part [0, 1, 2, 3, 5, 6] Ctx.Side.lower (by decide) (by decide)
  have hs2 : Ctx.Satisfies χ (lower 1) θ2 := by
    have h := (ctx_satisfies_of_deepBelowSplit θ1 hwf1 hs1 (hdeep 1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
    rw [hpos1, hmax1] at h
    exact h
  have hwf2 : θ2.WellFormed :=
    hwf1.part [0, 1, 2, 3, 6] Ctx.Side.lower (by decide) (by decide)
  have hs3 : Ctx.Satisfies χ (lower 2) θ3 := by
    have h := (ctx_satisfies_of_deepBelowSplit θ2 hwf2 hs2 (hdeep 2)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
    rw [hpos2, hmax2] at h
    exact h
  have hσ : θ3 = σ := rfl
  refine ⟨hdec, hdec.isSweepRealizable, hdeep 0, hdeep 1, hdeep 2,
    hsingle 3, hsingle 4, hsingle 5, hprofile, hσ, ?_⟩
  simpa only [hσ] using hs3

end ErdosSzekeres
