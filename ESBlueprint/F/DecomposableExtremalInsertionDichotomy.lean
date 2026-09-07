import ErdosSzekeres.DecomposableRealization

namespace ErdosSzekeres

/-- Under the explicit previous-size decomposable upper bound, a failed insertion into a decomposable extremal support either splits the support into exactly equal sweep halves or has a strong predecessor polygon lying entirely on one side whose extension by the new vertex fails. This isolates balanced cuts and endpoint compatibility without importing an unproved upper theorem.
@node
@ws F
@kind formalization
@consumer ErdosSzekeres.decomposable_extremal_insertion -/
theorem decomposable_extremal_insertion_dichotomy {n k : ℕ} {χ : TripleColoring n} {S : Finset (Fin n)} {q : Fin n}
  (hk : 4 ≤ k) (hprev : DecomposableExactUpperAt (k - 1))
  (hχ : IsSweepRealizable χ) (hSdec : IsDecomposableOn χ S)
  (hScard : S.card = 2 ^ (k - 2)) (hqS : q ∉ S)
  (hno : ¬ContainsStrongPolygonSet χ (insert q S) k) :
  (((S.filter (· < q)).card = 2 ^ (k - 3) ∧
    (S.filter (q < ·)).card = 2 ^ (k - 3)) ∨
   ∃ P : Finset (Fin n), P ⊆ S ∧ P.card = k - 1 ∧
    IsStrongPolygonSet χ P ∧
    ((∀ x ∈ P, x < q) ∨ (∀ x ∈ P, q < x)) ∧
    ¬IsStrongPolygonSet χ (insert q P)) := by
  classical

  -- Pull a deep-below split back along an increasing relabeling.  Empty
  -- preimages are allowed here; the recursive helper below removes them.
  have hdeepPullback :
      ∀ {m : ℕ} {lower upper : Finset (Fin n)}
          (f : Fin m ↪o Fin n),
        HasDeepBelowSplit χ lower upper →
          HasDeepBelowSplit (χ.restrict f)
            (Finset.univ.filter fun i => f i ∈ lower)
            (Finset.univ.filter fun i => f i ∈ upper) := by
    intro m lower upper f hdeep
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hiLower hiUpper
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiLower hiUpper
      exact (Finset.disjoint_left.mp hdeep.disjoint) hiLower hiUpper
    · intro t hi hj hl hnotLower hnotUpper
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi hj hl
      have hi' : f t.i ∈ lower ∪ upper := Finset.mem_union.mpr hi
      have hj' : f t.j ∈ lower ∪ upper := Finset.mem_union.mpr hj
      have hl' : f t.k ∈ lower ∪ upper := Finset.mem_union.mpr hl
      have hnotLower' :
          ¬(f t.i ∈ lower ∧ f t.j ∈ lower ∧ f t.k ∈ lower) := by
        rintro h
        apply hnotLower
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h
      have hnotUpper' :
          ¬(f t.i ∈ upper ∧ f t.j ∈ upper ∧ f t.k ∈ upper) := by
        rintro h
        apply hnotUpper
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h
      have hcolor := hdeep.crossing (t.map f) hi' hj' hl'
        hnotLower' hnotUpper'
      simpa only [TripleColoring.restrict_apply, OrderedTriple.map_j,
        Finset.mem_filter, Finset.mem_univ, true_and] using hcolor

  -- Pull an entire recursive decomposition back.  At a split, a child with
  -- empty preimage is discarded; if both preimages are nonempty, the pulled
  -- back deep-below split joins the two induction hypotheses.
  have hdecPullback :
      ∀ {support : Finset (Fin n)}, IsDecomposableOn χ support →
        ∀ {m : ℕ} (f : Fin m ↪o Fin n),
          (Finset.univ.filter fun i => f i ∈ support).Nonempty →
          IsDecomposableOn (χ.restrict f)
            (Finset.univ.filter fun i => f i ∈ support) := by
    intro support hdec
    induction hdec with
    | singleton x =>
        intro m f hne
        obtain ⟨i, hi⟩ := hne
        have hfi : f i = x := by simpa using hi
        have heq :
            (Finset.univ.filter fun j => f j ∈ ({x} : Finset (Fin n))) =
              {i} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · intro hfj
            exact f.injective (hfj.trans hfi.symm)
          · rintro rfl
            exact hfi
        rw [heq]
        exact IsDecomposableOn.singleton i
    | @split lower upper hlower hupper hdeep ihlower ihupper =>
        intro m f hne
        let lower' : Finset (Fin m) :=
          Finset.univ.filter fun i => f i ∈ lower
        let upper' : Finset (Fin m) :=
          Finset.univ.filter fun i => f i ∈ upper
        have hroot :
            (Finset.univ.filter fun i => f i ∈ lower ∪ upper) =
              lower' ∪ upper' := by
          ext i
          simp [lower', upper']
        rw [hroot]
        by_cases hlowerNe : lower'.Nonempty
        · by_cases hupperNe : upper'.Nonempty
          · have hdl : IsDecomposableOn (χ.restrict f) lower' := by
              simpa [lower'] using ihlower f
                (by simpa [lower'] using hlowerNe)
            have hdu : IsDecomposableOn (χ.restrict f) upper' := by
              simpa [upper'] using ihupper f
                (by simpa [upper'] using hupperNe)
            have hdeep' :
                HasDeepBelowSplit (χ.restrict f) lower' upper' := by
              simpa [lower', upper'] using hdeepPullback f hdeep
            exact IsDecomposableOn.split hdl hdu hdeep'
          · have hupperEmpty : upper' = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hupperNe
            have hdl : IsDecomposableOn (χ.restrict f) lower' := by
              simpa [lower'] using ihlower f
                (by simpa [lower'] using hlowerNe)
            simpa [hupperEmpty] using hdl
        · by_cases hupperNe : upper'.Nonempty
          · have hlowerEmpty : lower' = ∅ :=
              Finset.not_nonempty_iff_eq_empty.mp hlowerNe
            have hdu : IsDecomposableOn (χ.restrict f) upper' := by
              simpa [upper'] using ihupper f
                (by simpa [upper'] using hupperNe)
            simpa [hlowerEmpty] using hdu
          · exfalso
            obtain ⟨i, hi⟩ := hne
            have hiUnion : i ∈ lower' ∪ upper' := by
              rw [← hroot]
              exact hi
            rcases Finset.mem_union.mp hiUnion with hiLower | hiUpper
            · exact hlowerNe ⟨i, hiLower⟩
            · exact hupperNe ⟨i, hiUpper⟩

  -- Specialize the pullback to the increasing enumeration of a nonempty
  -- support.  Its preimage is all of `Fin U.card`.
  have hdecRestrict :
      ∀ {U : Finset (Fin n)}, IsDecomposableOn χ U →
        IsDecomposable (χ.restrict (U.orderEmbOfFin rfl)) := by
    intro U hUdec
    let f : Fin U.card ↪o Fin n := U.orderEmbOfFin rfl
    have hpreimage :
        (Finset.univ.filter fun i : Fin U.card => f i ∈ U) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      exact U.orderEmbOfFin_mem rfl i
    have hpreimageNe :
        (Finset.univ.filter fun i : Fin U.card => f i ∈ U).Nonempty := by
      rw [hpreimage]
      have hUpos : 0 < U.card := Finset.card_pos.mpr hUdec.nonempty
      exact ⟨⟨0, hUpos⟩, Finset.mem_univ _⟩
    have hpull := hdecPullback hUdec f hpreimageNe
    change IsDecomposableOn (χ.restrict f) Finset.univ
    simpa only [hpreimage] using hpull

  -- Minimal witness transport, copied here to avoid importing the much
  -- larger structural-charging transport layer.
  have hmapStrong :
      ∀ {m r : ℕ} (f : Fin m ↪o Fin n),
        ContainsStrongPolygonSet (χ.restrict f) Finset.univ r →
          ContainsStrongPolygonSet χ (Finset.univ.image f) r := by
    intro m r f h
    obtain ⟨polygon, _, hcard, hstrong⟩ := h
    let e : Fin r ↪o Fin m := polygon.orderEmbOfFin hcard
    have heStrong : IsStrongPolygonOn (χ.restrict f) e := by
      intro i j a b hij hja hab
      exact hstrong (e.strictMono hij) (e.strictMono hja)
        (e.strictMono hab)
        (polygon.orderEmbOfFin_mem hcard i)
        (polygon.orderEmbOfFin_mem hcard j)
        (polygon.orderEmbOfFin_mem hcard a)
        (polygon.orderEmbOfFin_mem hcard b)
    let g : Fin r ↪o Fin n := e.trans f
    have hgStrong : IsStrongPolygonOn χ g := by
      intro i j a b hij hja hab
      exact heStrong hij hja hab
    refine ⟨Finset.univ.image g, ?_, ?_,
      FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hgStrong⟩
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      exact ⟨e i, rfl⟩
    · simpa using Finset.card_image_of_injective Finset.univ g.injective

  -- The explicit predecessor theorem gives a strong `(k-1)`-set in every
  -- decomposable subset whose cardinality is strictly above half.
  have strongPredecessorOfLarge
      (U : Finset (Fin n)) (hUS : U ⊆ S)
      (hlarge : 2 ^ (k - 3) < U.card) :
      ContainsStrongPolygonSet χ U (k - 1) := by
    have hUne : U.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hlarge)
    have hUdec : IsDecomposableOn χ U := hSdec.subset hUS hUne
    let f : Fin U.card ↪o Fin n := U.orderEmbOfFin rfl
    have hreal : IsSweepRealizable (χ.restrict f) := hχ.restrict f
    have hdec : IsDecomposable (χ.restrict f) := by
      dsimp only [f]
      exact hdecRestrict hUdec
    have hlarge' : 2 ^ ((k - 1) - 2) < U.card := by
      rw [show (k - 1) - 2 = k - 3 by omega]
      exact hlarge
    have hrestricted :
        ContainsStrongPolygonSet (χ.restrict f) Finset.univ (k - 1) :=
      hprev hreal hdec hlarge'
    have hmapped := hmapStrong f hrestricted
    have himage : Finset.univ.image f = U := by
      dsimp only [f]
      exact Finset.image_orderEmbOfFin_univ U rfl
    simpa only [himage] using hmapped

  let before : Finset (Fin n) := S.filter (· < q)
  let after : Finset (Fin n) := S.filter (q < ·)
  let half : ℕ := 2 ^ (k - 3)
  change (before.card = half ∧ after.card = half) ∨
    ∃ P : Finset (Fin n),
      P ⊆ S ∧ P.card = k - 1 ∧ IsStrongPolygonSet χ P ∧
        ((∀ x ∈ P, x < q) ∨ (∀ x ∈ P, q < x)) ∧
        ¬IsStrongPolygonSet χ (insert q P)
  have hbeforeSub : before ⊆ S := Finset.filter_subset _ _
  have hafterSub : after ⊆ S := Finset.filter_subset _ _
  have hdisjoint : Disjoint before after := by
    rw [Finset.disjoint_left]
    intro x hxBefore hxAfter
    have hxq : x < q := (Finset.mem_filter.mp hxBefore).2
    have hqx : q < x := (Finset.mem_filter.mp hxAfter).2
    omega
  have hunion : before ∪ after = S := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with hxBefore | hxAfter
      · exact hbeforeSub hxBefore
      · exact hafterSub hxAfter
    · intro hxS
      have hxne : x ≠ q := by
        intro hxq
        subst x
        exact hqS hxS
      rcases lt_or_gt_of_ne hxne with hxq | hqx
      · exact Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hxS, hxq⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hxS, hqx⟩)
  have hsum : before.card + after.card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  have hpow : 2 ^ (k - 2) = 2 * half := by
    rw [show k - 2 = (k - 3) + 1 by omega, pow_succ]
    simp only [half, Nat.mul_comm]
  have hsumHalf : before.card + after.card = 2 * half :=
    hsum.trans (hScard.trans hpow)
  by_cases hbeforeEq : before.card = half
  · exact Or.inl ⟨hbeforeEq, by omega⟩
  · have hlarge : half < before.card ∨ half < after.card := by omega
    rcases hlarge with hbeforeLarge | hafterLarge
    · obtain ⟨P, hPbefore, hPcard, hPstrong⟩ :=
        strongPredecessorOfLarge before hbeforeSub (by simpa [half] using hbeforeLarge)
      have hPS : P ⊆ S := hPbefore.trans hbeforeSub
      have hPside : ∀ x ∈ P, x < q := by
        intro x hxP
        exact (Finset.mem_filter.mp (hPbefore hxP)).2
      have hqP : q ∉ P := fun hqP => hqS (hPS hqP)
      have hnotInsert : ¬IsStrongPolygonSet χ (insert q P) := by
        intro hstrong
        apply hno
        refine ⟨insert q P, Finset.insert_subset_insert q hPS, ?_, hstrong⟩
        rw [Finset.card_insert_of_notMem hqP, hPcard]
        omega
      exact Or.inr ⟨P, hPS, hPcard, hPstrong, Or.inl hPside,
        hnotInsert⟩
    · obtain ⟨P, hPafter, hPcard, hPstrong⟩ :=
        strongPredecessorOfLarge after hafterSub (by simpa [half] using hafterLarge)
      have hPS : P ⊆ S := hPafter.trans hafterSub
      have hPside : ∀ x ∈ P, q < x := by
        intro x hxP
        exact (Finset.mem_filter.mp (hPafter hxP)).2
      have hqP : q ∉ P := fun hqP => hqS (hPS hqP)
      have hnotInsert : ¬IsStrongPolygonSet χ (insert q P) := by
        intro hstrong
        apply hno
        refine ⟨insert q P, Finset.insert_subset_insert q hPS, ?_, hstrong⟩
        rw [Finset.card_insert_of_notMem hqP, hPcard]
        omega
      exact Or.inr ⟨P, hPS, hPcard, hPstrong, Or.inr hPside,
        hnotInsert⟩

end ErdosSzekeres
