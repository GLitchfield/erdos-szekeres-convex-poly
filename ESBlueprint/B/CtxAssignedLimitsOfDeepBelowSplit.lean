import ErdosSzekeres.DecomposableContext
import ESBlueprint.B.CtxPartEndpointPathLifting
import ESBlueprint.B.CtxPartLimitsLe
import ESBlueprint.B.DeepSplitFiniteEndpointConstraintsIff
import ESBlueprint.B.DeepSplitStrongAvoidanceIff

namespace ErdosSzekeres

/-- For any deep-below split with monotone assigned slot labels, distinct cross labels and explicit opposite-marker membership in the two context parts, complete child cup/cap endpoint limits and no strong k-set transfer to the parent. Includes empty chains and zero/one/two selected endpoints; root coupling follows from zero-gain limits. No wellformedness, occupancy, joint-placement or maximum hypothesis.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.ctx_part_endpoint_path_lifting, ErdosSzekeres.ctx_part_limits_le, ErdosSzekeres.deepSplit_finite_endpoint_constraints_iff, ErdosSzekeres.deepSplit_two_endpoint_extensions, ErdosSzekeres.deepSplit_strong_avoidance_iff
@dangling-ok General missing fixed-root assigned-slot transfer for virtual B constructions and exact endpoint-profile composition; stable placement and fuel induction remain separate general obligations, not finite cases or upper assertions. -/
theorem ctx_assigned_limits_of_deepBelowSplit {n : ℕ} (σ : Ctx.Context) (hk : 3 ≤ σ.k) (keepL keepU : List ℕ)
(α β : ℕ) (hshare : α + β = σ.k - 1)
{χ : TripleColoring n} {lower upper : Finset (Fin n)}
(hdeep : HasDeepBelowSplit χ lower upper)
(z : Fin n → ℕ) (hz : Monotone z)
(hlabels : ∀ p ∈ lower, ∀ q ∈ upper, z p ≠ z q)
(hsideL : (σ.part keepL Ctx.Side.lower β).sideAt 1 = Ctx.Side.lower)
(hsideU : (σ.part keepU Ctx.Side.upper α).sideAt 1 = Ctx.Side.upper)
(hmarkL : ∀ q ∈ upper, z q ∈ (σ.part keepL Ctx.Side.lower β).extPositions 1)
(hmarkU : ∀ p ∈ lower, z p ∈ (σ.part keepU Ctx.Side.upper α).extPositions 1) :
let allowed (τ : Ctx.Context) (c : Turn) (T : Finset (Fin n)) : Prop :=
  ∀ p ∈ T, ∀ q ∈ T, (∀ i ∈ T, p ≤ i) → (∀ i ∈ T, i ≤ q) →
    T.card ≤ if c = Turn.left then τ.cupLimit (z p) (z q) else τ.capLimit (z p) (z q)
let bounded (τ : Ctx.Context) (S : Finset (Fin n)) : Prop :=
  (∀ T : Finset (Fin n), T ⊆ S → IsCupSet χ T → allowed τ Turn.left T) ∧
  (∀ T : Finset (Fin n), T ⊆ S → IsCapSet χ T → allowed τ Turn.right T)
bounded (σ.part keepL Ctx.Side.lower β) lower →
bounded (σ.part keepU Ctx.Side.upper α) upper →
¬ ContainsStrongPolygonSet χ lower σ.k →
¬ ContainsStrongPolygonSet χ upper σ.k →
bounded σ (lower ∪ upper) ∧ ¬ ContainsStrongPolygonSet χ (lower ∪ upper) σ.k := by
  classical
  dsimp only
  let applies (lim : ℕ → ℕ → ℕ) (T : Finset (Fin n)) : Prop :=
    ∀ p ∈ T, ∀ q ∈ T, (∀ i ∈ T, p ≤ i) → (∀ i ∈ T, i ≤ q) →
      T.card ≤ lim (z p) (z q)
  let growth (τ : Ctx.Context) (s : Ctx.Side) : ℕ → ℕ → ℕ :=
    match s with
    | Ctx.Side.lower => τ.cupLimit
    | Ctx.Side.upper => τ.capLimit
  change
    ((∀ T, T ⊆ lower → IsCupSet χ T →
        applies (σ.part keepL Ctx.Side.lower β).cupLimit T) ∧
     (∀ T, T ⊆ lower → IsCapSet χ T →
        applies (σ.part keepL Ctx.Side.lower β).capLimit T)) →
    ((∀ T, T ⊆ upper → IsCupSet χ T →
        applies (σ.part keepU Ctx.Side.upper α).cupLimit T) ∧
     (∀ T, T ⊆ upper → IsCapSet χ T →
        applies (σ.part keepU Ctx.Side.upper α).capLimit T)) → _
  intro hL hU hnoL hnoU
  have gain (ψ : TripleColoring n) (S O : Finset (Fin n))
      (keep : List ℕ) (s : Ctx.Side) (m : ℕ)
      (hside : (σ.part keep s m).sideAt 1 = s)
      (hsep : ∀ p ∈ S, ∀ q ∈ O, z p ≠ z q)
      (hmark : ∀ q ∈ O, z q ∈ (σ.part keep s m).extPositions 1)
      (hcore : ∀ C, C ⊆ S → IsCupSet ψ C → applies (growth (σ.part keep s m) s) C)
      (C : Finset (Fin n)) (hCS : C ⊆ S) (hC : IsCupSet ψ C) (hne : C.Nonempty)
      (p : Fin n) (hp : p ∈ C) (q : Fin n) (hq : q ∈ C)
      (hmin : ∀ i ∈ C, p ≤ i) (hmax : ∀ i ∈ C, i ≤ q)
      (x y : Fin n) (eL eR : Bool)
      (hx : if eL then x ∈ O ∧ x < p else x = p)
      (hy : if eR then y ∈ O ∧ q < y else y = q) :
      C.card + ((if eL then 1 else 0) + (if eR then 1 else 0)) ≤
        growth σ s (z x) (z y) := by
    have hzL : if eL then
        z x < z p ∧ z x ∈ (σ.part keep s m).extPositions 1 else z x = z p := by
      cases eL with
      | false => exact congrArg z hx
      | true =>
        change x ∈ O ∧ x < p at hx
        exact ⟨lt_of_le_of_ne (hz hx.2.le) (hsep p (hCS hp) x hx.1).symm,
          hmark x hx.1⟩
    have hzR : if eR then
        z q < z y ∧ z y ∈ (σ.part keep s m).extPositions 1 else z y = z q := by
      cases eR with
      | false => exact congrArg z hy
      | true =>
        change y ∈ O ∧ q < y at hy
        exact ⟨lt_of_le_of_ne (hz hy.2.le) (hsep q (hCS hq) y hy.1),
          hmark y hy.1⟩
    have hc := hcore C hCS hC p hp q hq hmin hmax
    have ht := ctx_part_endpoint_path_lifting σ keep s m hside
      (z p) (z q) (z x) (z y) eL eR hzL hzR
    cases s <;> exact (ht.2.2.2 C.card (Finset.card_pos.mpr hne) hc).1
  have cup_transfer (ψ : TripleColoring n) (S O : Finset (Fin n))
      (hd : HasDeepBelowSplit ψ S O) (lim child : ℕ → ℕ → ℕ)
      (hS : ∀ C, C ⊆ S → IsCupSet ψ C → applies lim C)
      (hO : ∀ C, C ⊆ O → IsCupSet ψ C → applies lim C)
      (hchild : ∀ C, C ⊆ S → IsCupSet ψ C → applies child C)
      (hgain : ∀ C, C ⊆ S → IsCupSet ψ C → C.Nonempty →
        ∀ p ∈ C, ∀ q ∈ C, (∀ i ∈ C, p ≤ i) → (∀ i ∈ C, i ≤ q) →
        ∀ x y : Fin n, ∀ eL eR : Bool,
        (if eL then x ∈ O ∧ x < p else x = p) →
        (if eR then y ∈ O ∧ q < y else y = q) →
        C.card + ((if eL then 1 else 0) + (if eR then 1 else 0)) ≤ lim (z x) (z y)) :
      ∀ T, T ⊆ S ∪ O → IsCupSet ψ T → applies lim T := by
    have one : ∀ C, C ⊆ S → IsCupSet ψ C → ∀ t ∈ O,
        HasDeepBelowSplit.IsSweepEndpoint C t → applies lim (insert t C) := by
      intro C hCS hC t ht hend
      by_cases hne : C.Nonempty
      · let a := C.min' hne
        let b := C.max' hne
        have ha : a ∈ C := C.min'_mem hne
        have hb : b ∈ C := C.max'_mem hne
        have hamin : ∀ i ∈ C, a ≤ i := fun i hi ↦ C.min'_le i hi
        have hbmax : ∀ i ∈ C, i ≤ b := fun i hi ↦ C.le_max' i hi
        have hnot : t ∉ C := fun hc ↦ Finset.disjoint_left.mp hd.disjoint (hCS hc) ht
        have hcard : (insert t C).card = C.card + 1 := Finset.card_insert_of_notMem hnot
        intro p hp q hq hpmin hqmax
        rcases hend with hleft | hright
        · have hta : t < a := lt_of_le_of_ne (hleft a ha) (by
            intro heq; apply hnot; simpa only [heq] using ha)
          have hpEq : p = t := le_antisymm (hpmin t (Finset.mem_insert_self t C)) (by
            rcases Finset.mem_insert.mp hp with heq | hpC
            · exact heq.symm.le
            · exact hleft p hpC)
          have hqEq : q = b := le_antisymm (by
            rcases Finset.mem_insert.mp hq with heq | hqC
            · simpa only [heq] using hleft b hb
            · exact hbmax q hqC) (hqmax b (Finset.mem_insert_of_mem hb))
          have hg := hgain C hCS hC hne a ha b hb hamin hbmax t b true false
            ⟨ht, hta⟩ rfl
          rw [hpEq, hqEq, hcard]
          simpa using hg
        · have hbt : b < t := lt_of_le_of_ne (hright b hb) (by
            intro heq; apply hnot; simpa only [← heq] using hb)
          have hpEq : p = a := le_antisymm (hpmin a (Finset.mem_insert_of_mem ha)) (by
            rcases Finset.mem_insert.mp hp with heq | hpC
            · simpa only [heq] using hright a ha
            · exact hamin p hpC)
          have hqEq : q = t := le_antisymm (by
            rcases Finset.mem_insert.mp hq with heq | hqC
            · exact heq.le
            · exact hright q hqC) (hqmax t (Finset.mem_insert_self t C))
          have hg := hgain C hCS hC hne a ha b hb hamin hbmax a t false true
            rfl ⟨ht, hbt⟩
          rw [hpEq, hqEq, hcard]
          simpa using hg
      · have hnil : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst C
        apply hO _ (by simp [ht])
        simpa using Ctx.isCupSet_singleton ψ t
    have two : ∀ C, C ⊆ S → IsCupSet ψ C → ∀ x y : Fin n,
        x ∈ O → y ∈ O → x < y → (∀ i ∈ C, x < i) → (∀ i ∈ C, i < y) →
        applies lim (insert x (insert y C)) := by
      intro C hCS hC x y hx hy hxy hleft hright
      by_cases hne : C.Nonempty
      · let a := C.min' hne
        let b := C.max' hne
        have ha : a ∈ C := C.min'_mem hne
        have hb : b ∈ C := C.max'_mem hne
        have hamin : ∀ i ∈ C, a ≤ i := fun i hi ↦ C.min'_le i hi
        have hbmax : ∀ i ∈ C, i ≤ b := fun i hi ↦ C.le_max' i hi
        have hynot : y ∉ C := fun hc ↦ Finset.disjoint_left.mp hd.disjoint (hCS hc) hy
        have hxnot : x ∉ insert y C := by
          intro h
          rcases Finset.mem_insert.mp h with heq | hxC
          · exact hxy.ne heq
          · exact Finset.disjoint_left.mp hd.disjoint (hCS hxC) hx
        have hcard : (insert x (insert y C)).card = C.card + 1 + 1 := by
          rw [Finset.card_insert_of_notMem hxnot, Finset.card_insert_of_notMem hynot]
        intro p hp q hq hpmin hqmax
        have hpEq : p = x := le_antisymm
          (hpmin x (Finset.mem_insert_self x (insert y C))) (by
            rcases Finset.mem_insert.mp hp with heq | hp'
            · exact heq.symm.le
            · rcases Finset.mem_insert.mp hp' with heq | hpC
              · simpa only [heq] using hxy.le
              · exact (hleft p hpC).le)
        have hqEq : q = y := le_antisymm (by
            rcases Finset.mem_insert.mp hq with heq | hq'
            · simpa only [heq] using hxy.le
            · rcases Finset.mem_insert.mp hq' with heq | hqC
              · exact heq.le
              · exact (hright q hqC).le)
          (hqmax y (Finset.mem_insert_of_mem (Finset.mem_insert_self y C)))
        have hg := hgain C hCS hC hne a ha b hb hamin hbmax x y true true
          ⟨hx, hleft a ha⟩ ⟨hy, hright b hb⟩
        rw [hpEq, hqEq, hcard]
        simpa [Nat.add_assoc] using hg
      · have hnil : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        apply hO _ (by simp [hnil, Finset.insert_subset_iff, hx, hy])
        exact (deepSplit_two_endpoint_extensions hd).1 C hCS hC x y hx hy hxy hleft hright
    have hall := (deepSplit_finite_endpoint_constraints_iff hd (applies lim)
      (fun _ ↦ True)).2 ⟨⟨hS, hO, one, two⟩,
        ⟨by intros; trivial, by intros; trivial, by intros; trivial, by intros; trivial⟩⟩
    exact hall.1
  have pureCupL : ∀ T, T ⊆ lower → IsCupSet χ T → applies σ.cupLimit T := by
    intro T hT hc p hp q hq hmin hmax
    exact (hL.1 T hT hc p hp q hq hmin hmax).trans
      (ctx_part_limits_le σ keepL Ctx.Side.lower β (z p) (z q)).1
  have pureCupU : ∀ T, T ⊆ upper → IsCupSet χ T → applies σ.cupLimit T := by
    intro T hT hc p hp q hq hmin hmax
    exact (hU.1 T hT hc p hp q hq hmin hmax).trans
      (ctx_part_limits_le σ keepU Ctx.Side.upper α (z p) (z q)).1
  have pureCapL : ∀ T, T ⊆ lower → IsCapSet χ T → applies σ.capLimit T := by
    intro T hT hc p hp q hq hmin hmax
    exact (hL.2 T hT hc p hp q hq hmin hmax).trans
      (ctx_part_limits_le σ keepL Ctx.Side.lower β (z p) (z q)).2
  have pureCapU : ∀ T, T ⊆ upper → IsCapSet χ T → applies σ.capLimit T := by
    intro T hT hc p hp q hq hmin hmax
    exact (hU.2 T hT hc p hp q hq hmin hmax).trans
      (ctx_part_limits_le σ keepU Ctx.Side.upper α (z p) (z q)).2
  have hgCup := gain χ lower upper keepL Ctx.Side.lower β hsideL hlabels hmarkL hL.1
  have hsepU : ∀ p ∈ upper, ∀ q ∈ lower, z p ≠ z q :=
    fun p hp q hq ↦ (hlabels q hq p hp).symm
  have childDual : ∀ T, T ⊆ upper → IsCupSet χ.dual T →
      applies (σ.part keepU Ctx.Side.upper α).capLimit T := by
    simpa only [isCupSet_dual_iff] using hU.2
  have hgCap := gain χ.dual upper lower keepU Ctx.Side.upper α
    hsideU hsepU hmarkU childDual
  constructor
  · change (∀ T, T ⊆ lower ∪ upper → IsCupSet χ T → applies σ.cupLimit T) ∧
      (∀ T, T ⊆ lower ∪ upper → IsCapSet χ T → applies σ.capLimit T)
    constructor
    · exact cup_transfer χ lower upper hdeep σ.cupLimit
        (σ.part keepL Ctx.Side.lower β).cupLimit pureCupL pureCupU hL.1 hgCup
    · have hcap := cup_transfer χ.dual upper lower hdeep.dual σ.capLimit
        (σ.part keepU Ctx.Side.upper α).capLimit
        (by simpa only [isCupSet_dual_iff] using pureCapU)
        (by simpa only [isCupSet_dual_iff] using pureCapL) childDual hgCap
      simpa only [isCupSet_dual_iff, Finset.union_comm] using hcap
  · have lowBound : ∀ C, C ⊆ lower → IsCupSet χ C → C.card ≤ α := by
      intro C hCS hC
      by_cases hne : C.Nonempty
      · let p := C.min' hne
        let q := C.max' hne
        have hc := hL.1 C hCS hC p (C.min'_mem hne) q (C.max'_mem hne)
          (fun i hi ↦ C.min'_le i hi) (fun i hi ↦ C.le_max' i hi)
        have ht := (ctx_part_endpoint_path_lifting σ keepL Ctx.Side.lower β hsideL
          (z p) (z q) (z p) (z q) false false rfl rfl).2.2.2
          C.card (Finset.card_pos.mpr hne) hc
        have h := ht.2
        omega
      · have hnil := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hnil]
    have upBound : ∀ D, D ⊆ upper → IsCapSet χ D → D.card ≤ β := by
      intro D hDS hD
      by_cases hne : D.Nonempty
      · let p := D.min' hne
        let q := D.max' hne
        have hc := hU.2 D hDS hD p (D.min'_mem hne) q (D.max'_mem hne)
          (fun i hi ↦ D.min'_le i hi) (fun i hi ↦ D.le_max' i hi)
        have ht := (ctx_part_endpoint_path_lifting σ keepU Ctx.Side.upper α hsideU
          (z p) (z q) (z p) (z q) false false rfl rfl).2.2.2
          D.card (Finset.card_pos.mpr hne) hc
        have h := ht.2
        omega
      · have hnil := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hnil]
    have heq : σ.k - 1 + 1 = σ.k := by omega
    have hcouple : ∀ C D : Finset (Fin n), C ⊆ lower → D ⊆ upper →
        IsCupSet χ C → IsCapSet χ D → C.card + D.card ≤ σ.k - 1 := by
      intro C D hCS hDS hC hD
      have hc := lowBound C hCS hC
      have hd := upBound D hDS hD
      omega
    have hn := (deepSplit_strong_avoidance_iff (s := σ.k - 1) hdeep).2
      ⟨by simpa only [heq] using hnoL, by simpa only [heq] using hnoU, hcouple⟩
    simpa only [heq] using hn


end ErdosSzekeres
