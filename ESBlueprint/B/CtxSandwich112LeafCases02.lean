import ErdosSzekeres.PublishedInductionSemantics
import ESBlueprint.B.CtxSatisfiesOfDeepBelowSplit
import ESBlueprint.B.CtxBasePascalCombine
import ESBlueprint.B.CtxBaseCrossAxisTransfer
import ESBlueprint.B.CtxBaseSandwich112Case0200
import ESBlueprint.B.CtxBaseSandwich112Case0210
import ESBlueprint.B.CtxBaseSandwich112Case0211
import ESBlueprint.B.CtxBaseSandwich112Case0300
import ESBlueprint.B.CtxBaseSandwich112Case0310
import ESBlueprint.B.CtxBaseSandwich112Case0311
import ESBlueprint.B.CtxSingleRunDescendantLeafBound

namespace ErdosSzekeres

open Ctx Ctx.Context
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Geometric leaf bounds for the (1,1,2) sandwich, family 02. Uniform in every well-formed external context and admissible coupling. All four orientations of the two inner cuts after isolating outer child 2. Explicit new-level extension paths feed the general descendant leaf estimate and the checked scalar allocations.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_112 -/
theorem ctx_sandwich_112_leaf_cases_02 (σ : Ctx.Context) (hwf : σ.WellFormed) (b : ℕ) (hpos : σ.childPositions = List.range' b 4) :
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.lower (od)
      let M := σ.part [(b + 1)] Ctx.Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Ctx.Side.lower (e)
      let R := O.part [b, (b + 3)] Ctx.Side.upper (σ.k - 1 - e)
      let L := R.part [b] Ctx.Side.lower (f)
      let H := R.part [(b + 3)] Ctx.Side.upper (σ.k - 1 - f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound) ∧
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.lower (od)
      let M := σ.part [(b + 1)] Ctx.Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Ctx.Side.lower (e)
      let R := O.part [b, (b + 3)] Ctx.Side.upper (σ.k - 1 - e)
      let L := R.part [b] Ctx.Side.upper (σ.k - 1 - f)
      let H := R.part [(b + 3)] Ctx.Side.lower (f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound) ∧
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.lower (od)
      let M := σ.part [(b + 1)] Ctx.Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Ctx.Side.upper (σ.k - 1 - e)
      let R := O.part [b, (b + 3)] Ctx.Side.lower (e)
      let L := R.part [b] Ctx.Side.lower (f)
      let H := R.part [(b + 3)] Ctx.Side.upper (σ.k - 1 - f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound) ∧
  (∀ (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2),
      let O := σ.part [b, (b + 2), (b + 3)] Ctx.Side.lower (od)
      let M := σ.part [(b + 1)] Ctx.Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Ctx.Side.upper (σ.k - 1 - e)
      let R := O.part [b, (b + 3)] Ctx.Side.lower (e)
      let L := R.part [b] Ctx.Side.upper (σ.k - 1 - f)
      let H := R.part [(b + 3)] Ctx.Side.lower (f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound) := by
  have hrunBound : ∀ (τ : Context) (a n : ℕ), 0 < n →
      τ.childPositions = List.range' a n →
      τ.bound = baseOf (τ.cupLimit a a) (τ.capLimit a a) τ.k := by
    intro τ a n hn hps
    have hmem : ∀ p, p ∈ τ.childPositions ↔ a ≤ p ∧ p < a + n := by
      intro p
      rw [hps, List.mem_range'_1]
    let starts := (List.range τ.word.length).filter fun p ↦
      τ.letterAt p = Letter.child ∧ (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child)
    have hsubset : starts.toFinset ⊆ ({a} : Finset ℕ) := by
      intro p hp
      have hstart : p < τ.word.length ∧ τ.letterAt p = Letter.child ∧
          (p = 0 ∨ τ.letterAt (p - 1) ≠ Letter.child) := by
        simpa [starts] using hp
      have hp' := (hmem p).1
        (by simpa [childPositions] using And.intro hstart.1 hstart.2.1)
      simp only [Finset.mem_singleton]
      by_contra hpa
      have hprev : p - 1 ∈ τ.childPositions := (hmem (p - 1)).2 ⟨by omega, by omega⟩
      have hprev' : τ.letterAt (p - 1) = Letter.child :=
        (List.mem_filter.1 hprev).2 |> of_decide_eq_true
      rcases hstart.2.2 with hz | hnot
      · omega
      · exact hnot hprev'
    have hruns : τ.numRuns ≤ 1 := by
      calc
        τ.numRuns = starts.toFinset.card :=
          (List.toFinset_card_of_nodup (List.nodup_range.filter _)).symm
        _ ≤ ({a} : Finset ℕ).card := Finset.card_le_card hsubset
        _ = 1 := by simp
    simp [bound, boundFuel, hruns, base_eq_baseOf, hps, List.head?_range', Nat.ne_of_gt hn]
  let Anc (π : Context) (D : ℕ) : Prop :=
    π.a = σ.a ∧ π.u = σ.u ∧ π.k = σ.k ∧ π.maxima.length = D + σ.maxima.length ∧
      (∀ N, 1 ≤ N → π.extPositions (N + D) = σ.extPositions N) ∧
      (∀ N, 1 ≤ N → π.sideAt (N + D) = σ.sideAt N) ∧
      (∀ N, 1 ≤ N → π.maximumAt (N + D) = σ.maximumAt N)
  have hAnc0 : Anc σ 0 := by simp [Anc]
  have hAncPart (π : Context) (D : ℕ) (hπ : Anc π D) (keep : List ℕ) (s : Side) (m : ℕ) :
      Anc (π.part keep s m) (D + 1) := by
    obtain ⟨ha, hu, hk, hlen, hext, hside, hmax⟩ := hπ
    refine ⟨ha, hu, hk, ?_, ?_, ?_, ?_⟩
    · simp only [part_maxima, List.length_cons, hlen]; omega
    · intro N hN
      rw [← Nat.add_assoc, part_extPositions_succ π keep s m (by omega : 1 ≤ N + D)]
      exact hext N hN
    · intro N hN
      rw [← Nat.add_assoc, part_sideAt_succ π keep s m (by omega : 1 ≤ N + D)]
      exact hside N hN
    · intro N hN
      rw [← Nat.add_assoc, part_maximumAt_succ π keep s m (by omega : 1 ≤ N + D)]
      exact hmax N hN
  have hnewSub (π : Context) (D : ℕ) (hπ : Anc π D) (s : Side) (top : ℕ)
      (ls : List ℕ) (hls : ls.Sublist ((List.range D).map (· + 1)))
      (hs : ∀ l ∈ ls, π.sideAt l = s ∧ (top = 0 ∨ l < top)) :
      ls.Sublist (π.levelsOn s top) := by
    have hpre : ((List.range D).map (· + 1)).Sublist π.levels := by
      unfold levels
      rw [hπ.2.2.2.1, List.range_add, List.map_append]
      exact List.sublist_append_left _ _
    have hf : ls.filter (fun l => decide (π.sideAt l = s ∧ (top = 0 ∨ l < top))) = ls := by
      apply List.filter_eq_self.mpr
      intro l hl
      simp [hs l hl]
    have h := (hls.trans hpre).filter (fun l => decide (π.sideAt l = s ∧ (top = 0 ∨ l < top)))
    simpa only [hf, levelsOn] using h
  have hprefixSideSub (π : Context) (D : ℕ) (s : Side) (ls : List ℕ)
      (hls : ls.Sublist ((List.range D).map (· + 1)))
      (hs : ∀ l ∈ ls, π.sideAt l = s) :
      ls.Sublist (((List.range D).map (· + 1)).filter (fun l => π.sideAt l = s)) := by
    have hf : ls.filter (fun l => decide (π.sideAt l = s)) = ls := by
      apply List.filter_eq_self.mpr
      intro l hl
      simp [hs l hl]
    simpa only [hf] using hls.filter (fun l => decide (π.sideAt l = s))
  have hjoinNew (π : Context) (s : Side) (N p : ℕ)
      (hN : N ∈ π.levelsOn s 0) (L R : List ℕ)
      (hL : L.Sublist (π.levelsOn s N)) (hR : R.Sublist (π.levelsOn s N)) :
      (L.foldl (leftStep π) (p, 0)).2 + (R.foldl (rightStep π) (p, 0)).2 +
        π.maximumAt N ≤ π.joinExt s p p := by
    have hleft := le_getD_max?_of_mem (List.mem_map.mpr ⟨L, List.mem_sublists.mpr hL, rfl⟩ :
      (L.foldl (leftStep π) (p, 0)).2 ∈ (π.levelsOn s N).sublists.map (fun ls => (ls.foldl (leftStep π) (p, 0)).2))
    have hright := le_getD_max?_of_mem (List.mem_map.mpr ⟨R, List.mem_sublists.mpr hR, rfl⟩ :
      (R.foldl (rightStep π) (p, 0)).2 ∈ (π.levelsOn s N).sublists.map (fun ls => (ls.foldl (rightStep π) (p, 0)).2))
    change _ ≤ π.leftExt s N p at hleft
    change _ ≤ π.rightExt s N p at hright
    exact (Nat.add_le_add_right (Nat.add_le_add hleft hright) _).trans (le_joinExt_of_mem_levelsOn hN p p)
  have hleafEstimate := ctx_single_run_descendant_leaf_bound σ b 4 hpos (by decide)
  have hcombine := ctx_base_pascal_combine
  have hbaseSymm (x y k : ℕ) (hx : x ≤ k - 1) (hy : y ≤ k - 1) :
      baseOf x y k = baseOf y x k := by
    clear * - x y k hx hy
    have h := ctx_base_cross_axis_transfer 0 y x x k le_rfl hx (by simpa using hy)
    have h' := ctx_base_cross_axis_transfer 0 x y y k le_rfl hy (by simpa using hx)
    have hzL (n : ℕ) : baseOf 0 n k = 0 := by simp [baseOf]
    have hzR (n : ℕ) : baseOf n 0 k = 0 := by simp [baseOf]
    simp only [Nat.zero_add, Nat.add_zero, hzL, hzR] at h h'
    exact Nat.le_antisymm h h'
  have halloc_0200 := ctx_base_sandwich_112_case_0200
  have halloc_0201 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf C (min (P - 2) d) k +
        baseOf (min (C - 2) (min (k - 1 - e) (k - 1 - d - 2))) P k +
        baseOf (min (C - 1) (k - 1 - d)) (min (P - 1) (min f (e - 1))) k +
        baseOf (min (C - 1) (min (k - 1 - f) (k - 1 - d - 1))) (min (P - 1) e) k ≤ baseOf C P k := by
    have h := ctx_base_sandwich_112_case_0200 C P k d e f hC hP hd hdk he hek hf hfk
    omega
  have halloc_0210 := ctx_base_sandwich_112_case_0210
  have halloc_0211 := ctx_base_sandwich_112_case_0211
  have halloc_0300 := ctx_base_sandwich_112_case_0300
  have halloc_0301 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf C (min (P - 2) d) k +
        baseOf (min (C - 2) (min (k - 1 - e) (k - 1 - d - 1))) P k +
        baseOf (min (C - 1) (k - 1 - d)) (min (P - 2) (min f (e - 1))) k +
        baseOf (min (C - 1) (min (k - 1 - f) (k - 1 - d - 1))) (min (P - 1) e) k ≤ baseOf C P k := by
    have h := ctx_base_sandwich_112_case_0300 C P k d e f hC hP hd hdk he hek hf hfk
    omega
  have halloc_0310 := ctx_base_sandwich_112_case_0310
  have halloc_0311 := ctx_base_sandwich_112_case_0311
  have halloc_1200 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf (min (C - 2) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k +
        baseOf (min (C - 1) (k - 1 - f)) (min (P - 1) (min e (k - 1 - d - 1))) k +
        baseOf C (min (P - 2) (min f (min (e - 1) (k - 1 - d - 1)))) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0211
    have hlow := halloc_0211 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf (min (C - 2) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 2) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs2 : baseOf (min (C - 1) (k - 1 - f)) (min (P - 1) (min e (k - 1 - d - 1))) k = baseOf (min (P - 1) (min e (k - 1 - d - 1))) (min (C - 1) (k - 1 - f)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs3 : baseOf C (min (P - 2) (min f (min (e - 1) (k - 1 - d - 1)))) k = baseOf (min (P - 2) (min f (min (e - 1) (k - 1 - d - 1)))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have halloc_1201 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf (min (C - 2) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k +
        baseOf C (min (P - 1) (min f (min (e - 1) (k - 1 - d - 1)))) k +
        baseOf (min (C - 1) (k - 1 - f)) (min (P - 2) (min e (k - 1 - d - 1))) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0210
    have hlow := halloc_0210 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf (min (C - 2) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 2) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs2 : baseOf C (min (P - 1) (min f (min (e - 1) (k - 1 - d - 1)))) k = baseOf (min (P - 1) (min f (min (e - 1) (k - 1 - d - 1)))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs3 : baseOf (min (C - 1) (k - 1 - f)) (min (P - 2) (min e (k - 1 - d - 1))) k = baseOf (min (P - 2) (min e (k - 1 - d - 1))) (min (C - 1) (k - 1 - f)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have halloc_1210 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf C (min (P - 2) (min e (k - 1 - d - 2))) k +
        baseOf (min (C - 1) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k +
        baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0201
    have hlow := halloc_0201 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf C (min (P - 2) (min e (k - 1 - d - 2))) k = baseOf (min (P - 2) (min e (k - 1 - d - 2))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    have hs2 : baseOf (min (C - 1) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 1) (min (k - 1 - f) (k - 1 - e - 1))) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs3 : baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k = baseOf (min (P - 1) (min f (k - 1 - d - 1))) (min (C - 1) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have halloc_1211 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf C (min (P - 2) (min e (k - 1 - d - 2))) k +
        baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k +
        baseOf (min (C - 1) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0200
    have hlow := halloc_0200 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf C (min (P - 2) (min e (k - 1 - d - 2))) k = baseOf (min (P - 2) (min e (k - 1 - d - 2))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    have hs2 : baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k = baseOf (min (P - 1) (min f (k - 1 - d - 1))) (min (C - 1) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs3 : baseOf (min (C - 1) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 1) (min (k - 1 - f) (k - 1 - e - 1))) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have halloc_1300 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k +
        baseOf (min (C - 1) (k - 1 - f)) (min (P - 1) (min e (k - 1 - d - 1))) k +
        baseOf C (min (P - 2) (min f (min (e - 1) (k - 1 - d - 2)))) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0311
    have hlow := halloc_0311 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 1) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs2 : baseOf (min (C - 1) (k - 1 - f)) (min (P - 1) (min e (k - 1 - d - 1))) k = baseOf (min (P - 1) (min e (k - 1 - d - 1))) (min (C - 1) (k - 1 - f)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs3 : baseOf C (min (P - 2) (min f (min (e - 1) (k - 1 - d - 2)))) k = baseOf (min (P - 2) (min f (min (e - 1) (k - 1 - d - 2)))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have halloc_1301 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k +
        baseOf C (min (P - 2) (min f (min (e - 1) (k - 1 - d - 2)))) k +
        baseOf (min (C - 1) (k - 1 - f)) (min (P - 2) (min e (k - 1 - d - 1))) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0310
    have hlow := halloc_0310 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 1) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs2 : baseOf C (min (P - 2) (min f (min (e - 1) (k - 1 - d - 2)))) k = baseOf (min (P - 2) (min f (min (e - 1) (k - 1 - d - 2)))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    have hs3 : baseOf (min (C - 1) (k - 1 - f)) (min (P - 2) (min e (k - 1 - d - 1))) k = baseOf (min (P - 2) (min e (k - 1 - d - 1))) (min (C - 1) (k - 1 - f)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have halloc_1310 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf C (min (P - 2) (min e (k - 1 - d - 1))) k +
        baseOf (min (C - 2) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k +
        baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0301
    have hlow := halloc_0301 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf C (min (P - 2) (min e (k - 1 - d - 1))) k = baseOf (min (P - 2) (min e (k - 1 - d - 1))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    have hs2 : baseOf (min (C - 2) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 2) (min (k - 1 - f) (k - 1 - e - 1))) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs3 : baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k = baseOf (min (P - 1) (min f (k - 1 - d - 1))) (min (C - 1) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have halloc_1311 (C P k d e f : ℕ) (hC : C ≤ k - 1) (hP : P ≤ k - 1)
      (hd : 1 ≤ d) (hdk : d ≤ k - 2) (he : 1 ≤ e) (hek : e ≤ k - 2)
      (hf : 1 ≤ f) (hfk : f ≤ k - 2) :
      baseOf (min (C - 2) d) P k +
        baseOf C (min (P - 2) (min e (k - 1 - d - 1))) k +
        baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k +
        baseOf (min (C - 2) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k ≤ baseOf C P k := by
    clear * - C P k d e f hC hP hd hdk he hek hf hfk hbaseSymm halloc_0300
    have hlow := halloc_0300 P C k d (k - 1 - e) (k - 1 - f) hP hC hd hdk
      (by omega) (by omega) (by omega) (by omega)
    have hecomp : k - 1 - (k - 1 - e) = e := by omega
    have hfcomp : k - 1 - (k - 1 - f) = f := by omega
    simp only [hecomp, hfcomp] at hlow
    have hs0 : baseOf (min (C - 2) d) P k = baseOf P (min (C - 2) d) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) (hP)
    have hs1 : baseOf C (min (P - 2) (min e (k - 1 - d - 1))) k = baseOf (min (P - 2) (min e (k - 1 - d - 1))) C k :=
      hbaseSymm _ _ k (hC) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 2).trans hP))
    have hs2 : baseOf (min (C - 1) (k - 1 - e)) (min (P - 1) (min f (k - 1 - d - 1))) k = baseOf (min (P - 1) (min f (k - 1 - d - 1))) (min (C - 1) (k - 1 - e)) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 1).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    have hs3 : baseOf (min (C - 2) (min (k - 1 - f) (k - 1 - e - 1))) (min (P - 1) (k - 1 - d)) k = baseOf (min (P - 1) (k - 1 - d)) (min (C - 2) (min (k - 1 - f) (k - 1 - e - 1))) k :=
      hbaseSymm _ _ k ((Nat.min_le_left _ _).trans ((Nat.sub_le C 2).trans hC)) ((Nat.min_le_left _ _).trans ((Nat.sub_le P 1).trans hP))
    rw [hs0, hs1, hs2, hs3, hbaseSymm C P k hC hP]
    simpa only [min_assoc, min_left_comm, min_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlow
  have hquad_0200 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.lower (e)
      let R := O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)
      let L := R.part [b] Side.lower (f)
      let H := R.part [(b + 3)] Side.upper (σ.k - 1 - f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate halloc_0200
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.lower (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.lower (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.lower (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.upper (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.upper (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [(b + 2)] Side.lower (e)
      have hQw : Q.WellFormed := hOw.part [(b + 2)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [(b + 2)] Side.lower (e)
      have hQc : Q.childPositions = [(b + 2)] := by
        change (O.part [(b + 2)] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [b, (b + 3)] := by
        change (O.part [(b + 2)] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2)] Side.lower (e) (q := b)
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2)] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2)] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.lower := by
        change (O.part [(b + 2)] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2)] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [(b + 2)] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2)] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)
      have hRw : R.WellFormed := hOw.part [b, (b + 3)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [b, (b + 3)] Side.upper (σ.k - 1 - e)
      have hRc : R.childPositions = [b, (b + 3)] := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [(b + 2)] := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b, (b + 3)] Side.upper (σ.k - 1 - e) (q := (b + 2))
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = σ.k - 1 - e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b, (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.lower := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b, (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b, (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      let L := R.part [b] Side.lower (f)
      have hLw : L.WellFormed := hRw.part [b] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hLa : Anc L 3 := hAncPart R 2 hRa [b] Side.lower (f)
      have hLc : L.childPositions = [b] := by
        change (R.part [b] Side.lower (f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hLe1 : L.extPositions 1 = [(b + 3)] := by
        change (R.part [b] Side.lower (f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hLs1 : L.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [b] Side.lower (f) (q := (b + 3))
        change _ ∈ L.extPositions 1
        rw [hLe1]
        simp
      have hLm1 : L.maximumAt 1 = f := rfl
      have hLe2 : L.extPositions 2 = [(b + 2)] := by
        change (R.part [b] Side.lower (f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [b] Side.lower (f) (by decide : 1 ≤ 1), hRe1]
      have hLs2 : L.sideAt 2 = Side.upper := by
        change (R.part [b] Side.lower (f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 1), hRs1]
      have hLm2 : L.maximumAt 2 = σ.k - 1 - e := by
        change (R.part [b] Side.lower (f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 1), hRm1]
      have hLe3 : L.extPositions 3 = [(b + 1)] := by
        change (R.part [b] Side.lower (f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [b] Side.lower (f) (by decide : 1 ≤ 2), hRe2]
      have hLs3 : L.sideAt 3 = Side.lower := by
        change (R.part [b] Side.lower (f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 2), hRs2]
      have hLm3 : L.maximumAt 3 = od := by
        change (R.part [b] Side.lower (f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 2), hRm2]
      let H := R.part [(b + 3)] Side.upper (σ.k - 1 - f)
      have hHw : H.WellFormed := hRw.part [(b + 3)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hHa : Anc H 3 := hAncPart R 2 hRa [(b + 3)] Side.upper (σ.k - 1 - f)
      have hHc : H.childPositions = [(b + 3)] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hHe1 : H.extPositions 1 = [b] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hHs1 : H.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [(b + 3)] Side.upper (σ.k - 1 - f) (q := b)
        change _ ∈ H.extPositions 1
        rw [hHe1]
        simp
      have hHm1 : H.maximumAt 1 = σ.k - 1 - f := rfl
      have hHe2 : H.extPositions 2 = [(b + 2)] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRe1]
      have hHs2 : H.sideAt 2 = Side.upper := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRs1]
      have hHm2 : H.maximumAt 2 = σ.k - 1 - e := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRm1]
      have hHe3 : H.extPositions 3 = [(b + 1)] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRe2]
      have hHs3 : H.sideAt 3 = Side.lower := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRs2]
      have hHm3 : H.maximumAt 3 = od := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRm2]
      have hMbound : M.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k := by
        have hj0 : 0 ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hj1 : (σ.k - 1 - od) ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.upper 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.upper 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [] [] [1] [1]
          (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1]))
          (b + 1) (b + 1) b (b + 2) 0 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          0 (σ.k - 1 - od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (min ((σ.cupLimit b b) - 2) (min (σ.k - 1 - e) (σ.k - 1 - od - 2))) (σ.capLimit b b) σ.k := by
        have hj0 : (max (e) (od + 2)) ≤ Q.joinExt Side.lower (b + 2) (b + 2) := by
          have hjN1 := hjoinNew Q Side.lower 1 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew Q Side.lower 2 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [2] (by decide) (by simp [hQs1, hQs2]))) [1] [1]
            (hnewSub Q 2 hQa Side.lower 2 [1] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 2 [1] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : 0 ≤ Q.joinExt Side.upper (b + 2) (b + 2) := by
          exact Nat.zero_le _
        have hh := hleafEstimate Q 2 (b + 2) 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [1] [1] [] []
          (hprefixSideSub Q 2 Side.lower [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2]))
          b (b + 3) (b + 2) (b + 2) 1 1 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          (max (e) (od + 2)) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hLbound : L.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - f) (σ.k - 1 - od - 1))) (min ((σ.capLimit b b) - 1) e) σ.k := by
        have hj0 : (max (f) (od + 1)) ≤ L.joinExt Side.lower b b := by
          have hjN1 := hjoinNew L Side.lower 1 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] []
            (hnewSub L 3 hLa Side.lower 1 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 1 [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN1
          have hjN3 := hjoinNew L Side.lower 3 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [3] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] [1]
            (hnewSub L 3 hLa Side.lower 3 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 3 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : (σ.k - 1 - e) ≤ L.joinExt Side.upper b b := by
          have hjN2 := hjoinNew L Side.upper 2 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.upper 0 [2] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] []
            (hnewSub L 3 hLa Side.upper 2 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.upper 2 [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate L 3 b 1 hLa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hLc)
          [] [1] [] [2]
          (hprefixSideSub L 3 Side.lower [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.lower [1] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [2] (by decide) (by simp [hLs1, hLs2, hLs3]))
          b (b + 3) b (b + 2) 0 1 0 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc])
          (max (f) (od + 1)) (σ.k - 1 - e) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hHbound : H.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 1) (min f (e - 1))) σ.k := by
        have hj0 : (od) ≤ H.joinExt Side.lower (b + 3) (b + 3) := by
          have hjN3 := hjoinNew H Side.lower 3 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [3] (by decide) (by simp [hHs1, hHs2, hHs3]))) [] []
            (hnewSub H 3 hHa Side.lower 3 [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 3 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : (max (σ.k - 1 - f) (σ.k - 1 - e + 1)) ≤ H.joinExt Side.upper (b + 3) (b + 3) := by
          have hjN1 := hjoinNew H Side.upper 1 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.upper 0 [1] (by decide) (by simp [hHs1, hHs2, hHs3]))) [] []
            (hnewSub H 3 hHa Side.upper 1 [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.upper 1 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew H Side.upper 2 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.upper 0 [2] (by decide) (by simp [hHs1, hHs2, hHs3]))) [1] []
            (hnewSub H 3 hHa Side.upper 2 [1] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.upper 2 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate H 3 (b + 3) 1 hHa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hHc)
          [3] [] [1] []
          (hprefixSideSub H 3 Side.lower [3] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.lower [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [1] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          (b + 1) (b + 3) b (b + 3) 1 0 1 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc])
          (od) (max (σ.k - 1 - f) (σ.k - 1 - e + 1)) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + L.bound + H.bound ≤ _
      have hn := halloc_0200 (σ.cupLimit b b) (σ.capLimit b b) σ.k od e f hC hP hod hodk he hek hf hfk
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hLbound) hHbound).trans hn
  have hquad_0201 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.lower (e)
      let R := O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)
      let L := R.part [b] Side.upper (σ.k - 1 - f)
      let H := R.part [(b + 3)] Side.lower (f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate halloc_0201
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.lower (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.lower (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.lower (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.upper (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.upper (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [(b + 2)] Side.lower (e)
      have hQw : Q.WellFormed := hOw.part [(b + 2)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [(b + 2)] Side.lower (e)
      have hQc : Q.childPositions = [(b + 2)] := by
        change (O.part [(b + 2)] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [b, (b + 3)] := by
        change (O.part [(b + 2)] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2)] Side.lower (e) (q := b)
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2)] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2)] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.lower := by
        change (O.part [(b + 2)] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2)] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [(b + 2)] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2)] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)
      have hRw : R.WellFormed := hOw.part [b, (b + 3)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [b, (b + 3)] Side.upper (σ.k - 1 - e)
      have hRc : R.childPositions = [b, (b + 3)] := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [(b + 2)] := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b, (b + 3)] Side.upper (σ.k - 1 - e) (q := (b + 2))
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = σ.k - 1 - e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b, (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.lower := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b, (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [b, (b + 3)] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b, (b + 3)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      let L := R.part [b] Side.upper (σ.k - 1 - f)
      have hLw : L.WellFormed := hRw.part [b] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hLa : Anc L 3 := hAncPart R 2 hRa [b] Side.upper (σ.k - 1 - f)
      have hLc : L.childPositions = [b] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hLe1 : L.extPositions 1 = [(b + 3)] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hLs1 : L.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [b] Side.upper (σ.k - 1 - f) (q := (b + 3))
        change _ ∈ L.extPositions 1
        rw [hLe1]
        simp
      have hLm1 : L.maximumAt 1 = σ.k - 1 - f := rfl
      have hLe2 : L.extPositions 2 = [(b + 2)] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRe1]
      have hLs2 : L.sideAt 2 = Side.upper := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRs1]
      have hLm2 : L.maximumAt 2 = σ.k - 1 - e := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRm1]
      have hLe3 : L.extPositions 3 = [(b + 1)] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRe2]
      have hLs3 : L.sideAt 3 = Side.lower := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRs2]
      have hLm3 : L.maximumAt 3 = od := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRm2]
      let H := R.part [(b + 3)] Side.lower (f)
      have hHw : H.WellFormed := hRw.part [(b + 3)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hHa : Anc H 3 := hAncPart R 2 hRa [(b + 3)] Side.lower (f)
      have hHc : H.childPositions = [(b + 3)] := by
        change (R.part [(b + 3)] Side.lower (f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hHe1 : H.extPositions 1 = [b] := by
        change (R.part [(b + 3)] Side.lower (f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hHs1 : H.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [(b + 3)] Side.lower (f) (q := b)
        change _ ∈ H.extPositions 1
        rw [hHe1]
        simp
      have hHm1 : H.maximumAt 1 = f := rfl
      have hHe2 : H.extPositions 2 = [(b + 2)] := by
        change (R.part [(b + 3)] Side.lower (f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 1), hRe1]
      have hHs2 : H.sideAt 2 = Side.upper := by
        change (R.part [(b + 3)] Side.lower (f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 1), hRs1]
      have hHm2 : H.maximumAt 2 = σ.k - 1 - e := by
        change (R.part [(b + 3)] Side.lower (f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 1), hRm1]
      have hHe3 : H.extPositions 3 = [(b + 1)] := by
        change (R.part [(b + 3)] Side.lower (f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 2), hRe2]
      have hHs3 : H.sideAt 3 = Side.lower := by
        change (R.part [(b + 3)] Side.lower (f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 2), hRs2]
      have hHm3 : H.maximumAt 3 = od := by
        change (R.part [(b + 3)] Side.lower (f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 2), hRm2]
      have hMbound : M.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k := by
        have hj0 : 0 ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hj1 : (σ.k - 1 - od) ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.upper 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.upper 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [] [] [1] [1]
          (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1]))
          (b + 1) (b + 1) b (b + 2) 0 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          0 (σ.k - 1 - od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (min ((σ.cupLimit b b) - 2) (min (σ.k - 1 - e) (σ.k - 1 - od - 2))) (σ.capLimit b b) σ.k := by
        have hj0 : (max (e) (od + 2)) ≤ Q.joinExt Side.lower (b + 2) (b + 2) := by
          have hjN1 := hjoinNew Q Side.lower 1 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew Q Side.lower 2 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [2] (by decide) (by simp [hQs1, hQs2]))) [1] [1]
            (hnewSub Q 2 hQa Side.lower 2 [1] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 2 [1] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : 0 ≤ Q.joinExt Side.upper (b + 2) (b + 2) := by
          exact Nat.zero_le _
        have hh := hleafEstimate Q 2 (b + 2) 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [1] [1] [] []
          (hprefixSideSub Q 2 Side.lower [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [] (by decide) (by simp [hQs1, hQs2]))
          b (b + 3) (b + 2) (b + 2) 1 1 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          (max (e) (od + 2)) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hLbound : L.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 1) (min f (e - 1))) σ.k := by
        have hj0 : (od) ≤ L.joinExt Side.lower b b := by
          have hjN3 := hjoinNew L Side.lower 3 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [3] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] []
            (hnewSub L 3 hLa Side.lower 3 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 3 [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : (max (σ.k - 1 - f) (σ.k - 1 - e + 1)) ≤ L.joinExt Side.upper b b := by
          have hjN1 := hjoinNew L Side.upper 1 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.upper 0 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] []
            (hnewSub L 3 hLa Side.upper 1 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.upper 1 [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew L Side.upper 2 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.upper 0 [2] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] [1]
            (hnewSub L 3 hLa Side.upper 2 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.upper 2 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate L 3 b 1 hLa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hLc)
          [] [3] [] [1]
          (hprefixSideSub L 3 Side.lower [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.lower [3] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [1] (by decide) (by simp [hLs1, hLs2, hLs3]))
          b (b + 1) b (b + 3) 0 1 0 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc])
          (od) (max (σ.k - 1 - f) (σ.k - 1 - e + 1)) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hHbound : H.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - f) (σ.k - 1 - od - 1))) (min ((σ.capLimit b b) - 1) e) σ.k := by
        have hj0 : (max (f) (od + 1)) ≤ H.joinExt Side.lower (b + 3) (b + 3) := by
          have hjN1 := hjoinNew H Side.lower 1 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [1] (by decide) (by simp [hHs1, hHs2, hHs3]))) [] []
            (hnewSub H 3 hHa Side.lower 1 [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 1 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN1
          have hjN3 := hjoinNew H Side.lower 3 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [3] (by decide) (by simp [hHs1, hHs2, hHs3]))) [1] []
            (hnewSub H 3 hHa Side.lower 3 [1] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 3 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : (σ.k - 1 - e) ≤ H.joinExt Side.upper (b + 3) (b + 3) := by
          have hjN2 := hjoinNew H Side.upper 2 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.upper 0 [2] (by decide) (by simp [hHs1, hHs2, hHs3]))) [] []
            (hnewSub H 3 hHa Side.upper 2 [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.upper 2 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN2
          omega
        have hh := hleafEstimate H 3 (b + 3) 1 hHa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hHc)
          [1] [] [2] []
          (hprefixSideSub H 3 Side.lower [1] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.lower [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [2] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          b (b + 3) (b + 2) (b + 3) 1 0 1 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc])
          (max (f) (od + 1)) (σ.k - 1 - e) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + L.bound + H.bound ≤ _
      have hn := halloc_0201 (σ.cupLimit b b) (σ.capLimit b b) σ.k od e f hC hP hod hodk he hek hf hfk
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hLbound) hHbound).trans hn
  have hquad_0210 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
      let R := O.part [b, (b + 3)] Side.lower (e)
      let L := R.part [b] Side.lower (f)
      let H := R.part [(b + 3)] Side.upper (σ.k - 1 - f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate halloc_0210
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.lower (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.lower (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.lower (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.upper (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.upper (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
      have hQw : Q.WellFormed := hOw.part [(b + 2)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [(b + 2)] Side.upper (σ.k - 1 - e)
      have hQc : Q.childPositions = [(b + 2)] := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [b, (b + 3)] := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2)] Side.upper (σ.k - 1 - e) (q := b)
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = σ.k - 1 - e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.lower := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [b, (b + 3)] Side.lower (e)
      have hRw : R.WellFormed := hOw.part [b, (b + 3)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [b, (b + 3)] Side.lower (e)
      have hRc : R.childPositions = [b, (b + 3)] := by
        change (O.part [b, (b + 3)] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [(b + 2)] := by
        change (O.part [b, (b + 3)] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b, (b + 3)] Side.lower (e) (q := (b + 2))
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [b, (b + 3)] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b, (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.lower := by
        change (O.part [b, (b + 3)] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b, (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [b, (b + 3)] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b, (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      let L := R.part [b] Side.lower (f)
      have hLw : L.WellFormed := hRw.part [b] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hLa : Anc L 3 := hAncPart R 2 hRa [b] Side.lower (f)
      have hLc : L.childPositions = [b] := by
        change (R.part [b] Side.lower (f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hLe1 : L.extPositions 1 = [(b + 3)] := by
        change (R.part [b] Side.lower (f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hLs1 : L.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [b] Side.lower (f) (q := (b + 3))
        change _ ∈ L.extPositions 1
        rw [hLe1]
        simp
      have hLm1 : L.maximumAt 1 = f := rfl
      have hLe2 : L.extPositions 2 = [(b + 2)] := by
        change (R.part [b] Side.lower (f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [b] Side.lower (f) (by decide : 1 ≤ 1), hRe1]
      have hLs2 : L.sideAt 2 = Side.lower := by
        change (R.part [b] Side.lower (f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 1), hRs1]
      have hLm2 : L.maximumAt 2 = e := by
        change (R.part [b] Side.lower (f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 1), hRm1]
      have hLe3 : L.extPositions 3 = [(b + 1)] := by
        change (R.part [b] Side.lower (f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [b] Side.lower (f) (by decide : 1 ≤ 2), hRe2]
      have hLs3 : L.sideAt 3 = Side.lower := by
        change (R.part [b] Side.lower (f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 2), hRs2]
      have hLm3 : L.maximumAt 3 = od := by
        change (R.part [b] Side.lower (f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [b] Side.lower (f) (by decide : 1 ≤ 2), hRm2]
      let H := R.part [(b + 3)] Side.upper (σ.k - 1 - f)
      have hHw : H.WellFormed := hRw.part [(b + 3)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hHa : Anc H 3 := hAncPart R 2 hRa [(b + 3)] Side.upper (σ.k - 1 - f)
      have hHc : H.childPositions = [(b + 3)] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hHe1 : H.extPositions 1 = [b] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hHs1 : H.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [(b + 3)] Side.upper (σ.k - 1 - f) (q := b)
        change _ ∈ H.extPositions 1
        rw [hHe1]
        simp
      have hHm1 : H.maximumAt 1 = σ.k - 1 - f := rfl
      have hHe2 : H.extPositions 2 = [(b + 2)] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRe1]
      have hHs2 : H.sideAt 2 = Side.lower := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRs1]
      have hHm2 : H.maximumAt 2 = e := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRm1]
      have hHe3 : H.extPositions 3 = [(b + 1)] := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRe2]
      have hHs3 : H.sideAt 3 = Side.lower := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRs2]
      have hHm3 : H.maximumAt 3 = od := by
        change (R.part [(b + 3)] Side.upper (σ.k - 1 - f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRm2]
      have hMbound : M.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k := by
        have hj0 : 0 ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hj1 : (σ.k - 1 - od) ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.upper 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.upper 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [] [] [1] [1]
          (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1]))
          (b + 1) (b + 1) b (b + 2) 0 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          0 (σ.k - 1 - od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 2) e) σ.k := by
        have hj0 : (od) ≤ Q.joinExt Side.lower (b + 2) (b + 2) := by
          have hjN2 := hjoinNew Q Side.lower 2 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [2] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.lower 2 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 2 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : (σ.k - 1 - e) ≤ Q.joinExt Side.upper (b + 2) (b + 2) := by
          have hjN1 := hjoinNew Q Side.upper 1 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.upper 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate Q 2 (b + 2) 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [2] [] [1] [1]
          (hprefixSideSub Q 2 Side.lower [2] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [1] (by decide) (by simp [hQs1, hQs2]))
          (b + 1) (b + 2) b (b + 3) 1 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          (od) (σ.k - 1 - e) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hLbound : L.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - f) (min (σ.k - 1 - e - 1) (σ.k - 1 - od - 1)))) (σ.capLimit b b) σ.k := by
        have hj0 : (max (max (f) (e + 1)) (od + 1)) ≤ L.joinExt Side.lower b b := by
          have hjN1 := hjoinNew L Side.lower 1 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] []
            (hnewSub L 3 hLa Side.lower 1 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 1 [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew L Side.lower 2 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [2] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] [1]
            (hnewSub L 3 hLa Side.lower 2 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 2 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN2
          have hjN3 := hjoinNew L Side.lower 3 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [3] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] [1]
            (hnewSub L 3 hLa Side.lower 3 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 3 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : 0 ≤ L.joinExt Side.upper b b := by
          exact Nat.zero_le _
        have hh := hleafEstimate L 3 b 1 hLa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hLc)
          [] [1] [] []
          (hprefixSideSub L 3 Side.lower [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.lower [1] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          b (b + 3) b b 0 1 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc])
          (max (max (f) (e + 1)) (od + 1)) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hHbound : H.bound ≤ baseOf (min ((σ.cupLimit b b) - 2) (min (σ.k - 1 - e) (σ.k - 1 - od - 1))) (min ((σ.capLimit b b) - 1) f) σ.k := by
        have hj0 : (max (e) (od + 1)) ≤ H.joinExt Side.lower (b + 3) (b + 3) := by
          have hjN2 := hjoinNew H Side.lower 2 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [2] (by decide) (by simp [hHs1, hHs2, hHs3]))) [] []
            (hnewSub H 3 hHa Side.lower 2 [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 2 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN2
          have hjN3 := hjoinNew H Side.lower 3 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [3] (by decide) (by simp [hHs1, hHs2, hHs3]))) [2] []
            (hnewSub H 3 hHa Side.lower 3 [2] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 3 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : (σ.k - 1 - f) ≤ H.joinExt Side.upper (b + 3) (b + 3) := by
          have hjN1 := hjoinNew H Side.upper 1 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.upper 0 [1] (by decide) (by simp [hHs1, hHs2, hHs3]))) [] []
            (hnewSub H 3 hHa Side.upper 1 [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.upper 1 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate H 3 (b + 3) 1 hHa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hHc)
          [2, 3] [] [1] []
          (hprefixSideSub H 3 Side.lower [2, 3] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.lower [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [1] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          (b + 1) (b + 3) b (b + 3) 2 0 1 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc])
          (max (e) (od + 1)) (σ.k - 1 - f) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + L.bound + H.bound ≤ _
      have hn := halloc_0210 (σ.cupLimit b b) (σ.capLimit b b) σ.k od e f hC hP hod hodk he hek hf hfk
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hLbound) hHbound).trans hn
  have hquad_0211 (od e f : ℕ) (hod : 1 ≤ od) (hodk : od ≤ σ.k - 2)
      (he : 1 ≤ e) (hek : e ≤ σ.k - 2) (hf : 1 ≤ f) (hfk : f ≤ σ.k - 2) :
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
      let R := O.part [b, (b + 3)] Side.lower (e)
      let L := R.part [b] Side.upper (σ.k - 1 - f)
      let H := R.part [(b + 3)] Side.lower (f)
      M.bound + Q.bound + L.bound + H.bound ≤ σ.bound := by
    as_aux_lemma =>
      clear * - σ hwf b hpos od e f hod hodk he hek hf hfk hrunBound Anc hAnc0 hAncPart hnewSub hprefixSideSub hjoinNew hleafEstimate halloc_0211
      dsimp only
      have hCP4 : σ.childPositions = [b, b + 1, b + 2, b + 3] := by
        simpa [List.range'_succ, Nat.add_assoc] using hpos
      have hC : σ.cupLimit b b ≤ σ.k - 1 := by unfold cupLimit; omega
      have hP : σ.capLimit b b ≤ σ.k - 1 := by unfold capLimit; omega
      let O := σ.part [b, (b + 2), (b + 3)] Side.lower (od)
      have hOw : O.WellFormed := hwf.part [b, (b + 2), (b + 3)] Side.lower (by omega) (by omega)
      have hOa : Anc O 1 := hAncPart σ 0 hAnc0 [b, (b + 2), (b + 3)] Side.lower (od)
      have hOc : O.childPositions = [b, (b + 2), (b + 3)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hOe1 : O.extPositions 1 = [(b + 1)] := by
        change (σ.part [b, (b + 2), (b + 3)] Side.lower (od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hOs1 : O.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [b, (b + 2), (b + 3)] Side.lower (od) (q := (b + 1))
        change _ ∈ O.extPositions 1
        rw [hOe1]
        simp
      have hOm1 : O.maximumAt 1 = od := rfl
      let M := σ.part [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMw : M.WellFormed := hwf.part [(b + 1)] Side.upper (by omega) (by omega)
      have hMa : Anc M 1 := hAncPart σ 0 hAnc0 [(b + 1)] Side.upper (σ.k - 1 - od)
      have hMc : M.childPositions = [(b + 1)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).childPositions = _
        rw [part_childPositions, hCP4]
        simp [Nat.add_assoc]
      have hMe1 : M.extPositions 1 = [b, (b + 2), (b + 3)] := by
        change (σ.part [(b + 1)] Side.upper (σ.k - 1 - od)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1), hCP4]
        simp [Nat.add_assoc]
      have hMs1 : M.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hwf.2.2.2.2.2 p l t hh).1) [(b + 1)] Side.upper (σ.k - 1 - od) (q := b)
        change _ ∈ M.extPositions 1
        rw [hMe1]
        simp
      have hMm1 : M.maximumAt 1 = σ.k - 1 - od := rfl
      let Q := O.part [(b + 2)] Side.upper (σ.k - 1 - e)
      have hQw : Q.WellFormed := hOw.part [(b + 2)] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hQa : Anc Q 2 := hAncPart O 1 hOa [(b + 2)] Side.upper (σ.k - 1 - e)
      have hQc : Q.childPositions = [(b + 2)] := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hQe1 : Q.extPositions 1 = [b, (b + 3)] := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hQs1 : Q.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [(b + 2)] Side.upper (σ.k - 1 - e) (q := b)
        change _ ∈ Q.extPositions 1
        rw [hQe1]
        simp
      have hQm1 : Q.maximumAt 1 = σ.k - 1 - e := rfl
      have hQe2 : Q.extPositions 2 = [(b + 1)] := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [(b + 2)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOe1]
      have hQs2 : Q.sideAt 2 = Side.lower := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [(b + 2)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOs1]
      have hQm2 : Q.maximumAt 2 = od := by
        change (O.part [(b + 2)] Side.upper (σ.k - 1 - e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [(b + 2)] Side.upper (σ.k - 1 - e) (by decide : 1 ≤ 1), hOm1]
      let R := O.part [b, (b + 3)] Side.lower (e)
      have hRw : R.WellFormed := hOw.part [b, (b + 3)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hRa : Anc R 2 := hAncPart O 1 hOa [b, (b + 3)] Side.lower (e)
      have hRc : R.childPositions = [b, (b + 3)] := by
        change (O.part [b, (b + 3)] Side.lower (e)).childPositions = _
        rw [part_childPositions, hOc]
        simp [Nat.add_assoc]
      have hRe1 : R.extPositions 1 = [(b + 2)] := by
        change (O.part [b, (b + 3)] Side.lower (e)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1), hOc]
        simp [Nat.add_assoc]
      have hRs1 : R.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hOw.2.2.2.2.2 p l t hh).1) [b, (b + 3)] Side.lower (e) (q := (b + 2))
        change _ ∈ R.extPositions 1
        rw [hRe1]
        simp
      have hRm1 : R.maximumAt 1 = e := rfl
      have hRe2 : R.extPositions 2 = [(b + 1)] := by
        change (O.part [b, (b + 3)] Side.lower (e)).extPositions (1 + 1) = _
        rw [part_extPositions_succ O [b, (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOe1]
      have hRs2 : R.sideAt 2 = Side.lower := by
        change (O.part [b, (b + 3)] Side.lower (e)).sideAt (1 + 1) = _
        rw [part_sideAt_succ O [b, (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOs1]
      have hRm2 : R.maximumAt 2 = od := by
        change (O.part [b, (b + 3)] Side.lower (e)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ O [b, (b + 3)] Side.lower (e) (by decide : 1 ≤ 1), hOm1]
      let L := R.part [b] Side.upper (σ.k - 1 - f)
      have hLw : L.WellFormed := hRw.part [b] Side.upper (by omega) (by change _ ≤ σ.k - 2; omega)
      have hLa : Anc L 3 := hAncPart R 2 hRa [b] Side.upper (σ.k - 1 - f)
      have hLc : L.childPositions = [b] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hLe1 : L.extPositions 1 = [(b + 3)] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hLs1 : L.sideAt 1 = Side.upper := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [b] Side.upper (σ.k - 1 - f) (q := (b + 3))
        change _ ∈ L.extPositions 1
        rw [hLe1]
        simp
      have hLm1 : L.maximumAt 1 = σ.k - 1 - f := rfl
      have hLe2 : L.extPositions 2 = [(b + 2)] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRe1]
      have hLs2 : L.sideAt 2 = Side.lower := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRs1]
      have hLm2 : L.maximumAt 2 = e := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 1), hRm1]
      have hLe3 : L.extPositions 3 = [(b + 1)] := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRe2]
      have hLs3 : L.sideAt 3 = Side.lower := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRs2]
      have hLm3 : L.maximumAt 3 = od := by
        change (R.part [b] Side.upper (σ.k - 1 - f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [b] Side.upper (σ.k - 1 - f) (by decide : 1 ≤ 2), hRm2]
      let H := R.part [(b + 3)] Side.lower (f)
      have hHw : H.WellFormed := hRw.part [(b + 3)] Side.lower (by omega) (by change _ ≤ σ.k - 2; omega)
      have hHa : Anc H 3 := hAncPart R 2 hRa [(b + 3)] Side.lower (f)
      have hHc : H.childPositions = [(b + 3)] := by
        change (R.part [(b + 3)] Side.lower (f)).childPositions = _
        rw [part_childPositions, hRc]
        simp [Nat.add_assoc]
      have hHe1 : H.extPositions 1 = [b] := by
        change (R.part [(b + 3)] Side.lower (f)).extPositions 1 = _
        rw [part_extPositions_one (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1), hRc]
        simp [Nat.add_assoc]
      have hHs1 : H.sideAt 1 = Side.lower := by
        apply part_sideAt_one_of_mem (fun p l t hh => (hRw.2.2.2.2.2 p l t hh).1) [(b + 3)] Side.lower (f) (q := b)
        change _ ∈ H.extPositions 1
        rw [hHe1]
        simp
      have hHm1 : H.maximumAt 1 = f := rfl
      have hHe2 : H.extPositions 2 = [(b + 2)] := by
        change (R.part [(b + 3)] Side.lower (f)).extPositions (1 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 1), hRe1]
      have hHs2 : H.sideAt 2 = Side.lower := by
        change (R.part [(b + 3)] Side.lower (f)).sideAt (1 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 1), hRs1]
      have hHm2 : H.maximumAt 2 = e := by
        change (R.part [(b + 3)] Side.lower (f)).maximumAt (1 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 1), hRm1]
      have hHe3 : H.extPositions 3 = [(b + 1)] := by
        change (R.part [(b + 3)] Side.lower (f)).extPositions (2 + 1) = _
        rw [part_extPositions_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 2), hRe2]
      have hHs3 : H.sideAt 3 = Side.lower := by
        change (R.part [(b + 3)] Side.lower (f)).sideAt (2 + 1) = _
        rw [part_sideAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 2), hRs2]
      have hHm3 : H.maximumAt 3 = od := by
        change (R.part [(b + 3)] Side.lower (f)).maximumAt (2 + 1) = _
        rw [part_maximumAt_succ R [(b + 3)] Side.lower (f) (by decide : 1 ≤ 2), hRm2]
      have hMbound : M.bound ≤ baseOf (σ.cupLimit b b) (min ((σ.capLimit b b) - 2) od) σ.k := by
        have hj0 : 0 ≤ M.joinExt Side.lower (b + 1) (b + 1) := by
          exact Nat.zero_le _
        have hj1 : (σ.k - 1 - od) ≤ M.joinExt Side.upper (b + 1) (b + 1) := by
          have hjN1 := hjoinNew M Side.upper 1 (b + 1) (List.singleton_sublist.mp (hnewSub M 1 hMa Side.upper 0 [1] (by decide) (by simp [hMs1]))) [] []
            (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1])) (hnewSub M 1 hMa Side.upper 1 [] (by decide) (by simp [hMs1]))
          norm_num [leftStep, rightStep, hMe1, hMm1, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate M 1 (b + 1) 1 hMa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hMc)
          [] [] [1] [1]
          (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.lower [] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1])) (hprefixSideSub M 1 Side.upper [1] (by decide) (by simp [hMs1]))
          (b + 1) (b + 1) b (b + 2) 0 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc]) (by norm_num [leftStep, hMe1, Nat.add_assoc]) (by norm_num [rightStep, hMe1, Nat.add_assoc])
          0 (σ.k - 1 - od) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hQbound : Q.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (σ.k - 1 - od)) (min ((σ.capLimit b b) - 2) e) σ.k := by
        have hj0 : (od) ≤ Q.joinExt Side.lower (b + 2) (b + 2) := by
          have hjN2 := hjoinNew Q Side.lower 2 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.lower 0 [2] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.lower 2 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.lower 2 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN2
          omega
        have hj1 : (σ.k - 1 - e) ≤ Q.joinExt Side.upper (b + 2) (b + 2) := by
          have hjN1 := hjoinNew Q Side.upper 1 (b + 2) (List.singleton_sublist.mp (hnewSub Q 2 hQa Side.upper 0 [1] (by decide) (by simp [hQs1, hQs2]))) [] []
            (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2])) (hnewSub Q 2 hQa Side.upper 1 [] (by decide) (by simp [hQs1, hQs2]))
          norm_num [leftStep, rightStep, hQe1, hQe2, hQm1, hQm2, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate Q 2 (b + 2) 1 hQa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hQc)
          [2] [] [1] [1]
          (hprefixSideSub Q 2 Side.lower [2] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.lower [] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [1] (by decide) (by simp [hQs1, hQs2])) (hprefixSideSub Q 2 Side.upper [1] (by decide) (by simp [hQs1, hQs2]))
          (b + 1) (b + 2) b (b + 3) 1 0 1 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [leftStep, hQe1, hQe2, Nat.add_assoc]) (by norm_num [rightStep, hQe1, hQe2, Nat.add_assoc])
          (od) (σ.k - 1 - e) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hLbound : L.bound ≤ baseOf (min ((σ.cupLimit b b) - 1) (min (σ.k - 1 - e) (σ.k - 1 - od - 1))) (min ((σ.capLimit b b) - 1) f) σ.k := by
        have hj0 : (max (e) (od + 1)) ≤ L.joinExt Side.lower b b := by
          have hjN2 := hjoinNew L Side.lower 2 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [2] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] []
            (hnewSub L 3 hLa Side.lower 2 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 2 [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN2
          have hjN3 := hjoinNew L Side.lower 3 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.lower 0 [3] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] [2]
            (hnewSub L 3 hLa Side.lower 3 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.lower 3 [2] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : (σ.k - 1 - f) ≤ L.joinExt Side.upper b b := by
          have hjN1 := hjoinNew L Side.upper 1 b (List.singleton_sublist.mp (hnewSub L 3 hLa Side.upper 0 [1] (by decide) (by simp [hLs1, hLs2, hLs3]))) [] []
            (hnewSub L 3 hLa Side.upper 1 [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hnewSub L 3 hLa Side.upper 1 [] (by decide) (by simp [hLs1, hLs2, hLs3]))
          norm_num [leftStep, rightStep, hLe1, hLe2, hLe3, hLm1, hLm2, hLm3, Nat.add_assoc] at hjN1
          omega
        have hh := hleafEstimate L 3 b 1 hLa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hLc)
          [] [2] [] [1]
          (hprefixSideSub L 3 Side.lower [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.lower [2] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [] (by decide) (by simp [hLs1, hLs2, hLs3])) (hprefixSideSub L 3 Side.upper [1] (by decide) (by simp [hLs1, hLs2, hLs3]))
          b (b + 2) b (b + 3) 0 1 0 1
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [leftStep, hLe1, hLe2, hLe3, Nat.add_assoc]) (by norm_num [rightStep, hLe1, hLe2, hLe3, Nat.add_assoc])
          (max (e) (od + 1)) (σ.k - 1 - f) hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      have hHbound : H.bound ≤ baseOf (min ((σ.cupLimit b b) - 2) (min (σ.k - 1 - f) (min (σ.k - 1 - e - 1) (σ.k - 1 - od - 1)))) (σ.capLimit b b) σ.k := by
        have hj0 : (max (max (f) (e + 1)) (od + 1)) ≤ H.joinExt Side.lower (b + 3) (b + 3) := by
          have hjN1 := hjoinNew H Side.lower 1 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [1] (by decide) (by simp [hHs1, hHs2, hHs3]))) [] []
            (hnewSub H 3 hHa Side.lower 1 [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 1 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN1
          have hjN2 := hjoinNew H Side.lower 2 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [2] (by decide) (by simp [hHs1, hHs2, hHs3]))) [1] []
            (hnewSub H 3 hHa Side.lower 2 [1] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 2 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN2
          have hjN3 := hjoinNew H Side.lower 3 (b + 3) (List.singleton_sublist.mp (hnewSub H 3 hHa Side.lower 0 [3] (by decide) (by simp [hHs1, hHs2, hHs3]))) [1] []
            (hnewSub H 3 hHa Side.lower 3 [1] (by decide) (by simp [hHs1, hHs2, hHs3])) (hnewSub H 3 hHa Side.lower 3 [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          norm_num [leftStep, rightStep, hHe1, hHe2, hHe3, hHm1, hHm2, hHm3, Nat.add_assoc] at hjN3
          omega
        have hj1 : 0 ≤ H.joinExt Side.upper (b + 3) (b + 3) := by
          exact Nat.zero_le _
        have hh := hleafEstimate H 3 (b + 3) 1 hHa
          (by rw [hCP4]; simp) (by decide) (by simpa [List.range'_succ, Nat.add_assoc] using hHc)
          [2, 3] [] [] []
          (hprefixSideSub H 3 Side.lower [2, 3] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.lower [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [] (by decide) (by simp [hHs1, hHs2, hHs3])) (hprefixSideSub H 3 Side.upper [] (by decide) (by simp [hHs1, hHs2, hHs3]))
          (b + 1) (b + 3) (b + 3) (b + 3) 2 0 0 0
          (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp) (by rw [hCP4]; simp)
          (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [leftStep, hHe1, hHe2, hHe3, Nat.add_assoc]) (by norm_num [rightStep, hHe1, hHe2, hHe3, Nat.add_assoc])
          (max (max (f) (e + 1)) (od + 1)) 0 hj0 hj1
        exact hh.trans (baseOf_mono (by clear * - hC hP hod hodk he hek hf hfk; omega) (by clear * - hC hP hod hodk he hek hf hfk; omega))
      change M.bound + Q.bound + L.bound + H.bound ≤ _
      have hn := halloc_0211 (σ.cupLimit b b) (σ.capLimit b b) σ.k od e f hC hP hod hodk he hek hf hfk
      rw [hrunBound σ b 4 (by decide) hpos]
      exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hMbound hQbound) hLbound) hHbound).trans hn
  exact ⟨hquad_0200, hquad_0201, hquad_0210, hquad_0211⟩

end ErdosSzekeres
