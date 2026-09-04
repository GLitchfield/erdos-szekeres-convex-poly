module

public import ErdosSzekeres.TothValtrNormalization
public import ErdosSzekeres.Decomposable
public import ErdosSzekeres.SynchronizedFiveFanFin11WindowTransport
public import ErdosSzekeres.TripleColoringRealizability

@[expose] public section

/-!
# Anchored presentations

Every swept configuration can be re-presented, by an orientation-sign
preserving projective change of coordinates, so that its first vertex sees
every later pair as a right turn: after a quarter turn about the leftmost
point, a determinant-one shear making every other point lie to its right, and
the Tóth--Valtr chart with a small parameter, the sweep order of the remaining
points becomes their radial order around the anchor.

Strong polygon sets are preserved up to an index bijection, so any
finite certificate stated for anchored one-change colorings applies to every
sweep-realizable coloring.  This is the symmetry breaking that fixes the
`C(n-1,2)` triple colors through vertex `0` in the SAT instances for the
exact six-point case and for the fixed-six predecessor-half endpoint.
-/

namespace ErdosSzekeres

noncomputable section

/-- Vertex `0` sees every later pair as a right turn. -/
def SweptConfiguration.IsAnchored {m : ℕ} (C : SweptConfiguration (m + 1)) : Prop :=
  ∀ ⦃i j : Fin (m + 1)⦄, 0 < i → i < j → C.turn 0 i j = Turn.right

/-- The abstract anchor condition on a triple coloring. -/
def TripleColoring.IsAnchored {m : ℕ} (χ : TripleColoring (m + 1)) : Prop :=
  ∀ ⦃i j : Fin (m + 1)⦄ (hi : 0 < i) (hij : i < j), χ ⟨0, i, j, hi, hij⟩ = Turn.right

theorem SweptConfiguration.IsAnchored.tripleColoring {m : ℕ}
    {C : SweptConfiguration (m + 1)} (h : C.IsAnchored) :
    C.tripleColoring.IsAnchored :=
  fun _ _ hi hij => h hi hij

@[simp] theorem shear_zero (t : ℝ) : shear t 0 = 0 := by
  funext i
  fin_cases i <;> simp [shear, sweepCoordinate]

/-- Strong polygon sets of a swept configuration are exactly the index sets
whose points are in convex position. -/
theorem SweptConfiguration.isStrongPolygonSet_iff_inConvexPosition_image
    {n : ℕ} (Q : SweptConfiguration n) (t : Finset (Fin n)) :
    IsStrongPolygonSet Q.tripleColoring t ↔ InConvexPosition (t.image Q.point) := by
  classical
  let f : Fin t.card ↪o Fin n := t.orderEmbOfFin rfl
  have himage : Finset.univ.image f = t := Finset.image_orderEmbOfFin_univ t rfl
  have hpoints : (Q.restrict f).pointFinset = t.image Q.point := by
    ext x
    simp only [SweptConfiguration.pointFinset, Finset.mem_image, Finset.mem_univ, true_and,
      SweptConfiguration.restrict_point]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨f i, t.orderEmbOfFin_mem rfl i, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hrange : j ∈ Set.range (t.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hj
      obtain ⟨i, rfl⟩ := hrange
      exact ⟨i, rfl⟩
  have hkey : IsStrongPolygon (Q.restrict f).tripleColoring ↔
      IsStrongPolygonOn Q.tripleColoring f := by
    rw [Q.restrict_tripleColoring f]
    exact Iff.rfl
  constructor
  · intro h
    rw [← hpoints]
    exact (Q.restrict f).inConvexPosition_pointFinset_iff_isStrongPolygon.mpr
      (hkey.mpr (FinsetPolygon.IsStrongPolygonSet.isStrongPolygonOn_orderEmbOfFin h))
  · intro h
    rw [← hpoints] at h
    have hon : IsStrongPolygonOn Q.tripleColoring f :=
      hkey.mp ((Q.restrict f).inConvexPosition_pointFinset_iff_isStrongPolygon.mp h)
    have := FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hon
    rwa [himage] at this

theorem PreservesOrientationSignsOn.mono {f : Point 2 → Point 2}
    {s t : Finset (Point 2)} (h : PreservesOrientationSignsOn f s) (hts : t ⊆ s) :
    PreservesOrientationSignsOn f t :=
  fun _ ha _ hb _ hc => h (hts ha) (hts hb) (hts hc)

/-- An anchored re-presentation of a swept configuration, together with the
index bijection under which strong polygon sets correspond. -/
structure AnchoredReindexing {m : ℕ} (P : SweptConfiguration (m + 1)) where
  configuration : SweptConfiguration (m + 1)
  anchored : configuration.IsAnchored
  reindex : Fin (m + 1) ≃ Fin (m + 1)
  strong_iff : ∀ t : Finset (Fin (m + 1)),
    IsStrongPolygonSet P.tripleColoring t ↔
      IsStrongPolygonSet configuration.tripleColoring (t.map reindex.toEmbedding)

/-- Every swept configuration admits an anchored re-presentation. -/
theorem SweptConfiguration.exists_anchoredReindexing {m : ℕ}
    (P : SweptConfiguration (m + 1)) : Nonempty (AnchoredReindexing P) := by
  classical
  let z : Fin (m + 1) := 0
  let a : Point 2 := P.point z
  -- quarter turn about the anchor: second coordinates are nonnegative, positive away from it
  let centered : Point 2 → Point 2 := tothValtrQuarterTurnAt a
  have hcentered_one : ∀ i : Fin (m + 1), centered (P.point i) 1 = P.point i 0 - a 0 := by
    intro i
    simp [centered]
  have hy_nonneg : ∀ i : Fin (m + 1), 0 ≤ centered (P.point i) 1 := by
    intro i
    rw [hcentered_one]
    exact sub_nonneg.mpr (P.sweep_strictMono.monotone (Fin.zero_le i))
  have hy_pos : ∀ i : Fin (m + 1), i ≠ z → 0 < centered (P.point i) 1 := by
    intro i hi
    rw [hcentered_one]
    exact sub_pos.mpr (P.sweep_strictMono (Fin.pos_iff_ne_zero.mpr hi))
  -- shear parameter making every non-anchor first coordinate positive
  let μ : ℝ := 1 + ∑ i : Fin (m + 1),
    |centered (P.point i) 0| / centered (P.point i) 1
  have hterm_nonneg : ∀ i : Fin (m + 1),
      0 ≤ |centered (P.point i) 0| / centered (P.point i) 1 := by
    intro i
    exact div_nonneg (abs_nonneg _) (hy_nonneg i)
  let sheared : Point 2 → Point 2 := fun x => shear μ (centered x)
  have hsheared_zero : ∀ x, sheared x 0 = centered x 0 + μ * centered x 1 := by
    intro x
    simp [sheared, sweepCoordinate]
  have hsheared_one : ∀ x, sheared x 1 = centered x 1 := by
    intro x
    simp [sheared]
  have hx_pos : ∀ i : Fin (m + 1), i ≠ z → 0 < sheared (P.point i) 0 := by
    intro i hi
    rw [hsheared_zero]
    have hyi := hy_pos i hi
    have hsum : |centered (P.point i) 0| / centered (P.point i) 1 ≤
        ∑ j : Fin (m + 1), |centered (P.point j) 0| / centered (P.point j) 1 :=
      Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ i)
    have hμ : |centered (P.point i) 0| / centered (P.point i) 1 + 1 ≤ μ := by
      simp only [μ]
      linarith
    have hmul : |centered (P.point i) 0| + centered (P.point i) 1 ≤
        μ * centered (P.point i) 1 := by
      have := mul_le_mul_of_nonneg_right hμ (le_of_lt hyi)
      rwa [add_mul, div_mul_cancel₀ _ (ne_of_gt hyi), one_mul] at this
    have habs := neg_abs_le (centered (P.point i) 0)
    linarith
  -- the orientation of sheared centered points is the original orientation
  have hsheared_orientation : ∀ x y w : Point 2,
      orientation (sheared x) (sheared y) (sheared w) = orientation x y w := by
    intro x y w
    simp only [sheared, centered]
    rw [orientation_shear, orientation_tothValtrQuarterTurnAt]
  have hsheared_anchor : sheared a = 0 := by
    simp [sheared, centered]
  -- radial order of the remaining vertices
  let I := TothValtrRemainingIndex z
  let q : I → Point 2 := fun i => sheared (P.point i.val)
  have hqy : ∀ i : I, 0 < q i 1 := by
    intro i
    show 0 < sheared (P.point i.val) 1
    rw [hsheared_one]
    exact hy_pos i.val i.ne_anchor
  have hqx : ∀ i : I, 0 < q i 0 := fun i => hx_pos i.val i.ne_anchor
  have hradialInjective : Function.Injective (fun i : I => q i 0 / q i 1) := by
    intro i j hij
    apply TothValtrRemainingIndex.ext
    by_contra hneVal
    have hcross : q i 0 * q j 1 = q j 0 * q i 1 := by
      have := hij
      simp only at this
      field_simp [ne_of_gt (hqy i), ne_of_gt (hqy j)] at this
      linarith
    have hzero : orientation a (P.point i.val) (P.point j.val) = 0 := by
      rw [← hsheared_orientation, hsheared_anchor]
      simp only [orientation, Pi.zero_apply, sub_zero]
      change q i 0 * q j 1 - q i 1 * q j 0 = 0
      linarith
    exact P.generalPosition i.ne_anchor.symm j.ne_anchor.symm hneVal hzero
  letI : LinearOrder I := LinearOrder.lift' (fun i : I => q i 0 / q i 1) hradialInjective
  have hIcard : Fintype.card I = m := by
    let equiv : I ≃ {i : Fin (m + 1) // i ≠ z} :=
      { toFun := fun i => ⟨i.val, i.ne_anchor⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := by intro i; cases i; rfl
        right_inv := by intro i; cases i; rfl }
    rw [Fintype.card_congr equiv]
    simp [z, Fintype.card_subtype_compl]
  let e := Fintype.orderIsoFinOfCardEq I hIcard
  let p : Fin m → Point 2 := fun k => q (e k)
  have hpY : ∀ k, 0 < p k 1 := fun k => hqy (e k)
  have hpX : ∀ k, 0 < p k 0 := fun k => hqx (e k)
  have hpRadial : StrictMono fun k => p k 0 / p k 1 := by
    intro k l hkl
    change q (e k) 0 / q (e k) 1 < q (e l) 0 / q (e l) 1
    exact e.strictMono hkl
  obtain ⟨δ, hδ, hmono⟩ := exists_pos_tothValtrProjective_strictMono p hpY hpRadial
  -- the full coordinate change
  let F : Point 2 → Point 2 := fun x => tothValtrProjective δ (sheared x)
  have hFanchor : F a = 0 := by
    simp only [F, hsheared_anchor, tothValtrProjective_zero]
  have hhalf : ∀ x ∈ P.pointFinset, 0 < sheared x 1 + δ := by
    intro x hx
    simp only [SweptConfiguration.pointFinset, Finset.mem_image,
      Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    rw [hsheared_one]
    exact add_pos_of_nonneg_of_pos (hy_nonneg i) hδ
  have hFsigns : PreservesOrientationSignsOn F P.pointFinset := by
    intro x hx y hy w hw
    have hpos := orientation_tothValtrProjective_pos_iff δ
      (sheared x) (sheared y) (sheared w) hδ (hhalf x hx) (hhalf y hy) (hhalf w hw)
    have hneg := orientation_tothValtrProjective_neg_iff δ
      (sheared x) (sheared y) (sheared w) hδ (hhalf x hx) (hhalf y hy) (hhalf w hw)
    rw [hsheared_orientation] at hpos hneg
    exact ⟨hpos, hneg⟩
  have hFinjective : Set.InjOn F P.pointFinset := by
    intro x hx y hy hxy
    have hsh : sheared x = sheared y :=
      tothValtrProjective_injective_of_pos_denominators δ _ _ (ne_of_gt hδ)
        (hhalf x hx) (hhalf y hy) hxy
    have hcent : centered x = centered y := by
      have := congrArg (shear (-μ)) hsh
      simpa [sheared] using this
    exact tothValtrQuarterTurnAt_injective a hcent
  -- the anchored configuration
  let τ : Fin (m + 1) → Fin (m + 1) := Fin.cons z (fun k => (e k).val)
  have hτzero : τ 0 = z := by simp [τ]
  have hτsucc : ∀ k : Fin m, τ k.succ = (e k).val := by
    intro k
    simp [τ]
  have hτinjective : Function.Injective τ := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ l =>
        rw [hτzero, hτsucc] at hij
        exact absurd hij.symm (e l).ne_anchor
    | succ k =>
      induction j using Fin.cases with
      | zero =>
        rw [hτzero, hτsucc] at hij
        exact absurd hij (e k).ne_anchor
      | succ l =>
        rw [hτsucc, hτsucc] at hij
        have : e k = e l := TothValtrRemainingIndex.ext hij
        rw [e.injective this]
  have hτbijective : Function.Bijective τ :=
    (Finite.injective_iff_bijective).mp hτinjective
  let σ : Fin (m + 1) ≃ Fin (m + 1) := (Equiv.ofBijective τ hτbijective).symm
  have hτσ : ∀ i, τ (σ i) = i := by
    intro i
    exact (Equiv.ofBijective τ hτbijective).apply_symm_apply i
  let point : Fin (m + 1) → Point 2 := fun i => F (P.point (τ i))
  have hpoint_zero : point 0 = 0 := by
    simp only [point, hτzero]
    exact hFanchor
  have hpoint_succ : ∀ k : Fin m, point k.succ = tothValtrProjective δ (p k) := by
    intro k
    simp only [point, hτsucc]
    rfl
  have hproj_x_pos : ∀ k : Fin m, 0 < tothValtrProjective δ (p k) 0 := by
    intro k
    rw [tothValtrProjective_apply_zero]
    exact div_pos (hpX k) (add_pos (hpY k) hδ)
  have hsweep : StrictMono fun i => point i 0 := by
    rw [Fin.strictMono_iff_lt_succ]
    intro k
    show point k.castSucc 0 < point k.succ 0
    rw [hpoint_succ]
    by_cases hk : k.castSucc = 0
    · rw [hk, hpoint_zero]
      simpa using hproj_x_pos k
    · obtain ⟨k', hk'⟩ := Fin.exists_succ_eq.mpr hk
      rw [← hk', hpoint_succ]
      apply hmono
      rw [Fin.lt_def]
      have := congrArg Fin.val hk'
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
  have hgeneral : ∀ ⦃i j k : Fin (m + 1)⦄, i ≠ j → i ≠ k → j ≠ k →
      orientation (point i) (point j) (point k) ≠ 0 := by
    intro i j k hij hik hjk
    have hne : orientation (P.point (τ i)) (P.point (τ j)) (P.point (τ k)) ≠ 0 :=
      P.generalPosition (hτinjective.ne hij) (hτinjective.ne hik) (hτinjective.ne hjk)
    have hsign := hFsigns (P.mem_pointFinset (τ i)) (P.mem_pointFinset (τ j))
      (P.mem_pointFinset (τ k))
    intro hzero
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hsign.2.mpr hlt
      simp only [point] at hzero
      rw [hzero] at this
      exact lt_irrefl _ this
    · have := hsign.1.mpr hgt
      simp only [point] at hzero
      rw [hzero] at this
      exact lt_irrefl _ this
  let C : SweptConfiguration (m + 1) :=
    { point := point
      sweep_strictMono := hsweep
      generalPosition := hgeneral }
  have hCpoint : ∀ i, C.point (σ i) = F (P.point i) := by
    intro i
    change F (P.point (τ (σ i))) = F (P.point i)
    rw [hτσ]
  -- anchoring
  have hanchored : C.IsAnchored := by
    intro i j hi hij
    rw [C.turn_eq_right_iff 0 i j hi hij]
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp hi)
    obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.mpr (Fin.pos_iff_ne_zero.mp (lt_trans hi hij))
    have hkl : k < l := Fin.succ_lt_succ_iff.mp hij
    change orientation (point 0) (point k.succ) (point l.succ) < 0
    rw [hpoint_zero, hpoint_succ, hpoint_succ]
    have hradial := hpRadial hkl
    have hsource : orientation 0 (p k) (p l) < 0 := by
      rw [div_lt_div_iff₀ (hpY k) (hpY l)] at hradial
      simp only [orientation, Pi.zero_apply, sub_zero]
      nlinarith
    have hzeroDen : 0 < (0 : Point 2) 1 + δ := by simpa using hδ
    have := (orientation_tothValtrProjective_neg_iff δ 0 (p k) (p l) hδ hzeroDen
      (add_pos (hpY k) hδ) (add_pos (hpY l) hδ)).mpr hsource
    simpa [tothValtrProjective_zero] using this
  -- correspondence of strong polygon sets
  have hstrong : ∀ t : Finset (Fin (m + 1)),
      IsStrongPolygonSet P.tripleColoring t ↔
        IsStrongPolygonSet C.tripleColoring (t.map σ.toEmbedding) := by
    intro t
    rw [P.isStrongPolygonSet_iff_inConvexPosition_image,
      C.isStrongPolygonSet_iff_inConvexPosition_image]
    have himage : (t.map σ.toEmbedding).image C.point = (t.image P.point).image F := by
      rw [Finset.map_eq_image, Finset.image_image, Finset.image_image]
      apply Finset.image_congr
      intro i _
      exact hCpoint i
    rw [himage]
    have hsub : t.image P.point ⊆ P.pointFinset := by
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact P.mem_pointFinset i
    exact (inConvexPosition_image_iff_of_preservesOrientationSignsOn
      (P.pointFinset_generalPosition.mono hsub) (hFinjective.mono hsub)
      (hFsigns.mono hsub)).symm
  exact ⟨{ configuration := C, anchored := hanchored, reindex := σ, strong_iff := hstrong }⟩

namespace AnchoredReindexing

variable {m : ℕ} {P : SweptConfiguration (m + 1)} (A : AnchoredReindexing P)

theorem containsStrongPolygonSet_iff (s : Finset (Fin (m + 1))) (k : ℕ) :
    ContainsStrongPolygonSet P.tripleColoring s k ↔
      ContainsStrongPolygonSet A.configuration.tripleColoring
        (s.map A.reindex.toEmbedding) k := by
  constructor
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    refine ⟨polygon.map A.reindex.toEmbedding, Finset.map_subset_map.mpr hsub,
      by rw [Finset.card_map, hcard], (A.strong_iff polygon).mp hstrong⟩
  · rintro ⟨polygon, hsub, hcard, hstrong⟩
    refine ⟨polygon.map A.reindex.symm.toEmbedding, ?_, by rw [Finset.card_map, hcard], ?_⟩
    · intro i hi
      rw [Finset.mem_map_equiv] at hi
      have := hsub hi
      rw [Finset.mem_map_equiv] at this
      simpa using this
    · apply (A.strong_iff _).mpr
      have : (polygon.map A.reindex.symm.toEmbedding).map A.reindex.toEmbedding = polygon := by
        ext i
        simp
      rw [this]
      exact hstrong

theorem containsStrongPolygonSet_univ_iff (k : ℕ) :
    ContainsStrongPolygonSet P.tripleColoring Finset.univ k ↔
      ContainsStrongPolygonSet A.configuration.tripleColoring Finset.univ k := by
  rw [A.containsStrongPolygonSet_iff, Finset.map_univ_equiv]

end AnchoredReindexing

/-- A finite certificate for anchored one-change colorings on `m + 1` vertices
forces convex `k`-gons in every set of at least `m + 1` points. -/
theorem forcesConvexPolygon_of_anchored {m k : ℕ}
    (hsat : ∀ C : SweptConfiguration (m + 1), C.IsAnchored →
      ContainsStrongPolygonSet C.tripleColoring Finset.univ k) :
    ForcesConvexPolygon k (m + 1) := by
  intro s hcard hgp
  classical
  let R := Classical.choice (exists_sweptPresentation s hgp)
  let f : Fin (m + 1) ↪o Fin s.card := Fin.castLEOrderEmb hcard
  let P := R.configuration.restrict f
  let A := Classical.choice (P.exists_anchoredReindexing)
  have hC := hsat A.configuration A.anchored
  have hP : ContainsStrongPolygonSet P.tripleColoring Finset.univ k :=
    (A.containsStrongPolygonSet_univ_iff k).mpr hC
  obtain ⟨polygon, -, hpolygonCard, hstrong⟩ := hP
  rw [R.containsConvexSubset_iff_exists_isStrongPolygonOn k]
  subst hpolygonCard
  let g : Fin polygon.card ↪o Fin (m + 1) := polygon.orderEmbOfFin rfl
  refine ⟨g.trans f, ?_⟩
  have hon : IsStrongPolygonOn P.tripleColoring g :=
    FinsetPolygon.IsStrongPolygonSet.isStrongPolygonOn_orderEmbOfFin hstrong
  have hcolor : (R.configuration.tripleColoring.restrict f).restrict g =
      R.configuration.tripleColoring.restrict (g.trans f) := by
    funext t
    cases t
    rfl
  have hP' : P.tripleColoring = R.configuration.tripleColoring.restrict f :=
    R.configuration.restrict_tripleColoring f
  rw [IsStrongPolygonOn, hP'] at hon
  rw [IsStrongPolygonOn, ← hcolor]
  exact hon

end

end ErdosSzekeres

end
