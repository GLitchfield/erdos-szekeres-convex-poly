module

public import ErdosSzekeres.TothValtrOrderType

@[expose] public section

/-!
# Explicit normalization data for the Tóth--Valtr frame

This file implements the coordinate architecture selected for `FP-15.A`.
After an orientation-preserving quarter turn about the leftmost swept point,
all remaining points have positive second coordinate.  Their radial
coordinates are distinct.  A sufficiently small positive projective
parameter preserves that radial order and therefore supplies the cap anchor
condition.
-/

namespace ErdosSzekeres

noncomputable section

/-- Translate `anchor` to the origin and rotate counterclockwise by a quarter
turn. -/
def tothValtrQuarterTurnAt (anchor p : Point 2) : Point 2 :=
  ![-(p 1 - anchor 1), p 0 - anchor 0]

@[simp] theorem tothValtrQuarterTurnAt_apply_zero (anchor p : Point 2) :
    tothValtrQuarterTurnAt anchor p 0 = -(p 1 - anchor 1) := by
  simp [tothValtrQuarterTurnAt]

@[simp] theorem tothValtrQuarterTurnAt_apply_one (anchor p : Point 2) :
    tothValtrQuarterTurnAt anchor p 1 = p 0 - anchor 0 := by
  simp [tothValtrQuarterTurnAt]

@[simp] theorem tothValtrQuarterTurnAt_self (anchor : Point 2) :
    tothValtrQuarterTurnAt anchor anchor = 0 := by
  funext i
  fin_cases i <;> simp

/-- The centered quarter turn has determinant one. -/
@[simp] theorem orientation_tothValtrQuarterTurnAt
    (anchor a b c : Point 2) :
    orientation (tothValtrQuarterTurnAt anchor a)
        (tothValtrQuarterTurnAt anchor b)
        (tothValtrQuarterTurnAt anchor c) = orientation a b c := by
  simp only [orientation, tothValtrQuarterTurnAt_apply_zero,
    tothValtrQuarterTurnAt_apply_one]
  ring

/-- The centered quarter turn is injective. -/
theorem tothValtrQuarterTurnAt_injective (anchor : Point 2) :
    Function.Injective (tothValtrQuarterTurnAt anchor) := by
  intro a b h
  have hx := congrFun h 0
  have hy := congrFun h 1
  simp only [tothValtrQuarterTurnAt_apply_zero] at hx
  simp only [tothValtrQuarterTurnAt_apply_one] at hy
  funext i
  fin_cases i
  · change a 0 = b 0
    linarith
  · change a 1 = b 1
    linarith

/-- Radial order is stable under a sufficiently small positive projective
parameter for a finite family lying strictly above the anchor. -/
theorem exists_pos_tothValtrProjective_strictMono
    {n : ℕ} (p : Fin n → Point 2)
    (hy : ∀ i, 0 < p i 1)
    (hradial : StrictMono fun i => p i 0 / p i 1) :
    ∃ δ : ℝ, 0 < δ ∧
      StrictMono fun i => tothValtrProjective δ (p i) 0 := by
  have hevent : ∀ᶠ δ in nhds (0 : ℝ), ∀ i j, i < j →
      tothValtrProjective δ (p i) 0 <
        tothValtrProjective δ (p j) 0 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i < j
    · have hi : ContinuousAt (fun δ : ℝ => p i 0 / (p i 1 + δ)) 0 :=
        continuousAt_const.div (continuousAt_const.add continuousAt_id) <| by
          simpa using ne_of_gt (hy i)
      have hj : ContinuousAt (fun δ : ℝ => p j 0 / (p j 1 + δ)) 0 :=
        continuousAt_const.div (continuousAt_const.add continuousAt_id) <| by
          simpa using ne_of_gt (hy j)
      have hlt := hi.eventually_lt hj (by simpa using hradial hij)
      exact hlt.mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hij h).elim
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨ε / 2, by linarith, ?_⟩
  intro i j hij
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have hhalf : 0 ≤ ε / 2 := by linarith
  simp only [sub_zero]
  rw [abs_of_nonneg hhalf]
  linarith
  exact hij

/-- The indices remaining after the first swept point is selected as anchor. -/
structure TothValtrRemainingIndex {n : ℕ} (z : Fin n) where
  val : Fin n
  ne_anchor : val ≠ z
  deriving Fintype

@[ext] theorem TothValtrRemainingIndex.ext
    {n : ℕ} {z : Fin n} {i j : TothValtrRemainingIndex z}
    (h : i.val = j.val) : i = j := by
  cases i
  cases j
  cases h
  rfl

/-- The exact output of the coordinate normalization, before transferring
convex subsets back through the original swept presentation. -/
structure TothValtrNormalization {n : ℕ}
    (C : SweptConfiguration n) (hn : 0 < n) where
  delta : ℝ
  delta_pos : 0 < delta
  configuration : SweptConfiguration (n - 1)
  pointFinset_eq :
    configuration.pointFinset =
      (C.pointFinset.erase (C.point ⟨0, hn⟩)).image
        (fun p => tothValtrProjective delta
          (tothValtrQuarterTurnAt (C.point ⟨0, hn⟩) p))
  anchor_not_mem : (0 : Point 2) ∉ configuration.pointFinset
  anchor_pair_neg : ∀ ⦃i j : Fin (n - 1)⦄, i < j →
    orientation (configuration.point i) (configuration.point j) 0 < 0
  map_injective : Set.InjOn
    (fun p => tothValtrProjective delta
      (tothValtrQuarterTurnAt (C.point ⟨0, hn⟩) p)) C.pointFinset
  map_preserves_signs : PreservesOrientationSignsOn
    (fun p => tothValtrProjective delta
      (tothValtrQuarterTurnAt (C.point ⟨0, hn⟩) p)) C.pointFinset

/-- Every nonempty swept configuration admits the explicit Tóth--Valtr
normalization. -/
theorem SweptConfiguration.exists_tothValtrNormalization
    {n : ℕ} (C : SweptConfiguration n) (hn : 0 < n) :
    Nonempty (TothValtrNormalization C hn) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let z : Fin n := ⟨0, hn⟩
  let I := TothValtrRemainingIndex z
  let centered : I → Point 2 := fun i =>
    tothValtrQuarterTurnAt (C.point z) (C.point i.val)
  have hy : ∀ i, 0 < centered i 1 := by
    intro i
    rw [show centered i 1 = C.point i.val 0 - C.point z 0 by
      simp [centered]]
    exact sub_pos.mpr (C.sweep_strictMono <| by
      exact (Fin.pos_iff_ne_zero' i.val).2 (by simpa [z] using i.ne_anchor))
  have hradialInjective : Function.Injective
      (fun i : I => centered i 0 / centered i 1) := by
    intro i j hij
    apply TothValtrRemainingIndex.ext
    by_contra hneVal
    have hcross : centered i 0 * centered j 1 =
        centered j 0 * centered i 1 := by
      field_simp [ne_of_gt (hy i), ne_of_gt (hy j)] at hij
      simpa [mul_comm] using hij
    have hzero : orientation (C.point z) (C.point i.val) (C.point j.val) = 0 := by
      rw [← orientation_tothValtrQuarterTurnAt
        (C.point z) (C.point z) (C.point i.val) (C.point j.val)]
      rw [tothValtrQuarterTurnAt_self]
      simp only [orientation, Pi.zero_apply, sub_zero]
      change centered i 0 * centered j 1 - centered i 1 * centered j 0 = 0
      nlinarith
    exact C.generalPosition i.ne_anchor.symm j.ne_anchor.symm hneVal hzero
  letI : LinearOrder I := LinearOrder.lift'
    (fun i : I => centered i 0 / centered i 1) hradialInjective
  have hIcard : Fintype.card I = n - 1 := by
    let equiv : I ≃ {i : Fin n // i ≠ z} :=
      { toFun := fun i => ⟨i.val, i.ne_anchor⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := by intro i; cases i; rfl
        right_inv := by intro i; cases i; rfl }
    calc
      Fintype.card I = Fintype.card {i : Fin n // i ≠ z} :=
        Fintype.card_congr equiv
      _ = n - 1 := by
        simp [z, Fintype.card_subtype_compl]
  let e := Fintype.orderIsoFinOfCardEq I hIcard
  let p : Fin (n - 1) → Point 2 := fun i => centered (e i)
  have hpY : ∀ i, 0 < p i 1 := fun i => hy (e i)
  have hpRadial : StrictMono fun i => p i 0 / p i 1 := by
    intro i j hij
    change centered (e i) 0 / centered (e i) 1 <
      centered (e j) 0 / centered (e j) 1
    exact e.strictMono hij
  obtain ⟨δ, hδ, hmono⟩ :=
    exists_pos_tothValtrProjective_strictMono p hpY hpRadial
  let Q : SweptConfiguration (n - 1) :=
    { point := fun i => tothValtrProjective δ (p i)
      sweep_strictMono := hmono
      generalPosition := by
        intro i j k hij hik hjk
        have hpNe : orientation (p i) (p j) (p k) ≠ 0 := by
          rw [show orientation (p i) (p j) (p k) =
            orientation (C.point (e i).val) (C.point (e j).val)
              (C.point (e k).val) by
                simp [p, centered]]
          exact C.generalPosition
            (fun h => hij (e.injective (TothValtrRemainingIndex.ext h)))
            (fun h => hik (e.injective (TothValtrRemainingIndex.ext h)))
            (fun h => hjk (e.injective (TothValtrRemainingIndex.ext h)))
        rw [orientation_tothValtrProjective δ (p i) (p j) (p k)
          (ne_of_gt (add_pos (hpY i) hδ))
          (ne_of_gt (add_pos (hpY j) hδ))
          (ne_of_gt (add_pos (hpY k) hδ))]
        exact div_ne_zero (mul_ne_zero (ne_of_gt hδ) hpNe) <|
          mul_ne_zero
            (mul_ne_zero (ne_of_gt (add_pos (hpY i) hδ))
              (ne_of_gt (add_pos (hpY j) hδ)))
            (ne_of_gt (add_pos (hpY k) hδ)) }
  have hQpair : ∀ ⦃i j : Fin (n - 1)⦄, i < j →
      orientation (Q.point i) (Q.point j) 0 < 0 := by
    intro i j hij
    have hradial := hpRadial hij
    have hsource : orientation (p i) (p j) 0 < 0 := by
      rw [div_lt_div_iff₀ (hpY i) (hpY j)] at hradial
      simp only [orientation, Pi.zero_apply, zero_sub]
      nlinarith
    have hzeroDen : 0 < (0 : Point 2) 1 + δ := by simpa using hδ
    simpa [Q] using (orientation_tothValtrProjective_neg_iff
      δ (p i) (p j) 0 hδ
      (add_pos (hpY i) hδ) (add_pos (hpY j) hδ) hzeroDen).mpr hsource
  let F : Point 2 → Point 2 := fun x =>
    tothValtrProjective δ (tothValtrQuarterTurnAt (C.point z) x)
  have hhalf : ∀ x ∈ C.pointFinset,
      0 < tothValtrQuarterTurnAt (C.point z) x 1 + δ := by
    intro x hx
    simp only [SweptConfiguration.pointFinset, Finset.mem_image,
      Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [tothValtrQuarterTurnAt_apply_one]
    have hle : C.point z 0 ≤ C.point i 0 :=
      C.sweep_strictMono.monotone (Fin.zero_le i)
    linarith
  have hFinjective : Set.InjOn F C.pointFinset := by
    intro a ha b hb hab
    apply tothValtrQuarterTurnAt_injective (C.point z)
    apply tothValtrProjective_injective_of_pos_denominators
      δ _ _ (ne_of_gt hδ) (hhalf a ha) (hhalf b hb)
    exact hab
  have hFsigns : PreservesOrientationSignsOn F C.pointFinset := by
    intro a ha b hb c hc
    have hpos := orientation_tothValtrProjective_pos_iff δ
      (tothValtrQuarterTurnAt (C.point z) a)
      (tothValtrQuarterTurnAt (C.point z) b)
      (tothValtrQuarterTurnAt (C.point z) c)
      hδ (hhalf a ha) (hhalf b hb) (hhalf c hc)
    have hneg := orientation_tothValtrProjective_neg_iff δ
      (tothValtrQuarterTurnAt (C.point z) a)
      (tothValtrQuarterTurnAt (C.point z) b)
      (tothValtrQuarterTurnAt (C.point z) c)
      hδ (hhalf a ha) (hhalf b hb) (hhalf c hc)
    simpa [F] using And.intro hpos hneg
  have hpointFinset : Q.pointFinset =
      (C.pointFinset.erase (C.point z)).image F := by
    ext x
    constructor
    · intro hx
      simp only [SweptConfiguration.pointFinset, Finset.mem_image,
        Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      apply Finset.mem_image.mpr
      refine ⟨C.point (e i).val, ?_, ?_⟩
      · apply Finset.mem_erase.mpr
        refine ⟨?_, C.mem_pointFinset (e i).val⟩
        intro hpoint
        apply (e i).ne_anchor
        exact C.point_injective hpoint
      · rfl
    · intro hx
      obtain ⟨y, hyErase, hyMap⟩ := Finset.mem_image.mp hx
      have hyPoint := (Finset.mem_erase.mp hyErase).2
      simp only [SweptConfiguration.pointFinset, Finset.mem_image,
        Finset.mem_univ, true_and] at hyPoint
      obtain ⟨i, hiPoint⟩ := hyPoint
      subst y
      have hiNe : i ≠ z := by
        intro hi
        subst i
        exact (Finset.mem_erase.mp hyErase).1 rfl
      let ri : I := ⟨i, hiNe⟩
      obtain ⟨j, hj⟩ := e.surjective ri
      simp only [SweptConfiguration.pointFinset, Finset.mem_image,
        Finset.mem_univ, true_and]
      refine ⟨j, ?_⟩
      have hval : (e j).val = i := congrArg TothValtrRemainingIndex.val hj
      calc
        Q.point j = F (C.point i) := by simp [Q, p, centered, F, hval]
        _ = x := hyMap
  have hanchorNot : (0 : Point 2) ∉ Q.pointFinset := by
    intro hzero
    simp only [SweptConfiguration.pointFinset, Finset.mem_image,
      Finset.mem_univ, true_and] at hzero
    obtain ⟨i, hi⟩ := hzero
    have hyQ : 0 < Q.point i 1 := by
      change 0 < p i 1 / (p i 1 + δ)
      exact div_pos (hpY i) (add_pos (hpY i) hδ)
    have hiOne := congrFun hi 1
    simp only [Pi.zero_apply] at hiOne
    linarith
  refine ⟨
    { delta := δ
      delta_pos := hδ
      configuration := Q
      pointFinset_eq := by simpa [F, z] using hpointFinset
      anchor_not_mem := hanchorNot
      anchor_pair_neg := hQpair
      map_injective := by simpa [F, z] using hFinjective
      map_preserves_signs := by simpa [F, z] using hFsigns }⟩

end

end ErdosSzekeres

end
