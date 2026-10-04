import ErdosSzekeres.Decomposable
import ESBlueprint.B.DecomposableColoringPushforwardExists
import ErdosSzekeres.DecompositionPrimeMutationLocality
import ErdosSzekeres.DecomposableRealization

namespace ErdosSzekeres

/-- Every legal cap/cup/strong parameter has a decomposable sweep-realizable coloring attaining decomposableThreshold with cap and cup bounds and strong avoidance. Pascal and consecutive-window construction retaining decomposition; general lower leaf only.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.decomposable_coloring_pushforward_exists, ErdosSzekeres.IsDecomposableOn.of_agreeOnTriples, ErdosSzekeres.exists_deepComposition_coloring, ErdosSzekeres.IsStrongPolygonOn.card_le_of_crosses_deepSplit, ErdosSzekeres.IsDecomposable.isSweepRealizable
@dangling-ok General threshold lower leaf for virtual assigned-slot context-bound construction; upper threshold bound, joint slot placement and full B induction remain open. No finite-instance target or full maximum assertion. -/
theorem decomposable_threshold_lower_exists (a u k : ℕ) (hk : 3 ≤ k) (ha : 2 ≤ a) (hu : 2 ≤ u)
(hak : a ≤ k) (huk : u ≤ k) :
∃ χ : TripleColoring (decomposableThreshold a u k),
  IsDecomposable χ ∧ IsSweepRealizable χ ∧
  (∀ T : Finset (Fin (decomposableThreshold a u k)), IsCupSet χ T → T.card ≤ u - 1) ∧
  (∀ T : Finset (Fin (decomposableThreshold a u k)), IsCapSet χ T → T.card ≤ a - 1) ∧
  ¬ ContainsStrongPolygonSet χ Finset.univ k := by
  classical
  have image_decomp {v w : ℕ} (ψ : TripleColoring w) (f : Fin v ↪o Fin w)
      (h : IsDecomposable (ψ.restrict f)) :
      IsDecomposableOn ψ (Finset.univ.image f) := by
    obtain ⟨φ, hφ, hφd, _⟩ := decomposable_coloring_pushforward_exists (ψ.restrict f) f
    apply (hφd Finset.univ h).of_agreeOnTriples
    intro t hi hj hl
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hj
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hl
    let t' : OrderedTriple v := ⟨i, j, l,
      f.lt_iff_lt.mp (by simpa only [hi, hj] using t.hij),
      f.lt_iff_lt.mp (by simpa only [hj, hl] using t.hjk)⟩
    have ht : t'.map f = t := by
      cases t
      cases hi
      cases hj
      cases hl
      rfl
    have hh := congrFun hφ t'
    change φ (t'.map f) = ψ (t'.map f) at hh
    simpa only [ht] using hh
  have split_decomp {v w : ℕ} {ψ : TripleColoring (v + w)}
      (hs : HasDeepSplit ψ v)
      (hL : IsDecomposable (ψ.restrict (Fin.castAddOrderEmb w)))
      (hR : IsDecomposable (ψ.restrict (Fin.natAddOrderEmb v))) :
      IsDecomposable ψ := by
    have hbefore : (Finset.univ : Finset (Fin v)).image (Fin.castAddOrderEmb w) =
        indicesBefore (v + w) v := by
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_indicesBefore]
      constructor
      · rintro ⟨i, rfl⟩
        exact i.isLt
      · intro hz
        refine ⟨⟨z.val, hz⟩, ?_⟩
        apply Fin.ext
        rfl
    have hafter : (Finset.univ : Finset (Fin w)).image (Fin.natAddOrderEmb v) =
        indicesAfter (v + w) v := by
      ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_indicesAfter]
      constructor
      · rintro ⟨i, rfl⟩
        change v ≤ v + i.val
        omega
      · intro hz
        refine ⟨⟨z.val - v, by have := z.isLt; omega⟩, ?_⟩
        apply Fin.ext
        change v + (z.val - v) = z.val
        omega
    have hdL := image_decomp ψ (Fin.castAddOrderEmb w) hL
    have hdR := image_decomp ψ (Fin.natAddOrderEmb v) hR
    rw [hbefore] at hdL
    rw [hafter] at hdR
    have hd := IsDecomposableOn.split hdL hdR hs.toHasDeepBelowSplit
    simpa only [indicesBefore_union_indicesAfter] using hd
  have strong_bound {v w ac bc z : ℕ} {ψ : TripleColoring (v + w)}
      {ψL : TripleColoring v} {ψR : TripleColoring w}
      (hs : HasDeepSplit ψ v)
      (hL : ψ.restrict (Fin.castAddOrderEmb w) = ψL)
      (hR : ψ.restrict (Fin.natAddOrderEmb v) = ψR)
      (hLS : StrongPolygonSizeAtMost ψL z) (hRS : StrongPolygonSizeAtMost ψR z)
      (hLC : ChainSizeAtMost ψL Turn.left ac)
      (hRC : ChainSizeAtMost ψR Turn.right bc) (hc : ac + bc ≤ z) :
      StrongPolygonSizeAtMost ψ z := by
    intro r f hr
    by_cases hzero : leftCount f v = 0
    · have hall : ∀ i, v ≤ (f i).val := by
        intro i
        by_contra hn
        have hi := (lt_leftCount_iff f.strictMono v i).2 (show (f i).val < v by omega)
        omega
      exact strongPolygon_card_le_of_all_right hR f hr hall hRS
    · by_cases hright : r - leftCount f v = 0
      · have hcount : leftCount f v = r := by have := leftCount_le f v; omega
        have hall : ∀ i, (f i).val < v := by
          intro i
          rw [← lt_leftCount_iff f.strictMono v, hcount]
          exact i.isLt
        exact strongPolygon_card_le_of_all_left hL f hr hall hLS
      · exact (hr.card_le_of_crosses_deepSplit hs hL hR f
          (Nat.pos_of_ne_zero hzero) (Nat.pos_of_ne_zero hright) hLC hRC).trans hc
  have singleton_dec : IsDecomposable singletonConfiguration.tripleColoring := by
    have hU : (Finset.univ : Finset (Fin 1)) = {0} := by ext z; simp
    rw [IsDecomposable, hU]
    exact .singleton 0
  have classical_family : ∀ p q : ℕ,
      ∃ P : SweptConfiguration ((p + q).choose p),
        IsDecomposable P.tripleColoring ∧ HasPascalBounds P p q := by
    intro p q
    induction hN : p + q using Nat.strong_induction_on generalizing p q with
    | h N ih =>
      subst N
      rcases p with _ | p
      · rw [Nat.choose_zero_right]
        exact ⟨singletonConfiguration, singleton_dec, singleton_hasPascalBounds 0 q⟩
      · rcases q with _ | q
        · rw [Nat.choose_self]
          exact ⟨singletonConfiguration, singleton_dec, singleton_hasPascalBounds (p + 1) 0⟩
        · obtain ⟨A, hAd, hA⟩ := ih ((p + 1) + q) (by omega) (p + 1) q rfl
          obtain ⟨B, hBd, hB⟩ := ih (p + (q + 1)) (by omega) p (q + 1) rfl
          have hchoose : Nat.choose ((p + 1) + (q + 1)) (p + 1) =
              Nat.choose ((p + 1) + q) (p + 1) + Nat.choose (p + (q + 1)) p := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              Nat.choose_succ_succ' (p + q + 1) p
          rw [hchoose]
          obtain ⟨P, hs, hL, hR⟩ := exists_deepComposition_coloring A B
          refine ⟨P, split_decomp hs (by simpa only [hL] using hAd)
            (by simpa only [hR] using hBd), ⟨?_, ?_⟩⟩
          · constructor
            · simpa [HasCupCapBounds] using hs.cap_chainSizeAtMost hL hR hA.1.1 hB.1.1
            · simpa [HasCupCapBounds] using hs.cup_chainSizeAtMost hL hR hA.1.2 hB.1.2
          · apply strong_bound hs hL hR (ac := q + 1) (bc := p + 1)
            · intro r f hr
              have hh := hA.2 f hr
              have := Nat.le_max_right 1 ((p + 1) + (q + 1))
              have : max 1 ((p + 1) + q) ≤ max 1 ((p + 1) + (q + 1)) := by omega
              exact hh.trans this
            · intro r f hr
              have hh := hB.2 f hr
              have := Nat.le_max_right 1 ((p + 1) + (q + 1))
              have : max 1 (p + (q + 1)) ≤ max 1 ((p + 1) + (q + 1)) := by omega
              exact hh.trans this
            · exact hA.1.2
            · exact hB.1.1
            · have := Nat.le_max_right 1 ((p + 1) + (q + 1)); omega
  have windows (d L t : ℕ) (hd : 1 ≤ d) (hLt : L ≤ t) (htd : t ≤ d) :
      ∃ P : SweptConfiguration (∑ j ∈ Finset.Icc L t, Nat.choose d j),
        IsDecomposable P.tripleColoring ∧
        ChainSizeAtMost P.tripleColoring Turn.right (d - L + 1) ∧
        ChainSizeAtMost P.tripleColoring Turn.left (t + 1) ∧
        StrongPolygonSizeAtMost P.tripleColoring (d + 1) := by
    induction t with
    | zero =>
      have hL : L = 0 := by omega
      subst L
      have hsize : (∑ j ∈ Finset.Icc 0 0, Nat.choose d j) = Nat.choose (d + 0) d := by simp
      rw [hsize]
      obtain ⟨P, hPd, hP⟩ := classical_family d 0
      refine ⟨P, hPd, ?_, ?_, ?_⟩
      · simpa using hP.1.1
      · simpa using hP.1.2
      · intro r f hr
        have hh := hP.2 f hr
        have hm : max 1 (d + 0) = d := by omega
        rw [hm] at hh
        omega
    | succ t ih =>
      by_cases hbase : L = t + 1
      · subst L
        have hsize : (∑ j ∈ Finset.Icc (t + 1) (t + 1), Nat.choose d j) =
            Nat.choose ((d - (t + 1)) + (t + 1)) (d - (t + 1)) := by
          simp only [Finset.Icc_self, Finset.sum_singleton, Nat.sub_add_cancel htd]
          exact (Nat.choose_symm htd).symm
        rw [hsize]
        obtain ⟨P, hPd, hP⟩ := classical_family (d - (t + 1)) (t + 1)
        refine ⟨P, hPd, hP.1.1, hP.1.2, ?_⟩
        intro r f hr
        have hh := hP.2 f hr
        have hm : max 1 ((d - (t + 1)) + (t + 1)) = d := by omega
        rw [hm] at hh
        omega
      · have hLt' : L ≤ t := by omega
        obtain ⟨A, hAd, hAcap, hAcup, hAS⟩ := ih hLt' (by omega)
        have hchoose : Nat.choose ((d - (t + 1)) + (t + 1)) (d - (t + 1)) =
            Nat.choose d (t + 1) := by
          rw [Nat.sub_add_cancel htd]
          exact Nat.choose_symm htd
        have hBex : ∃ B : SweptConfiguration (Nat.choose d (t + 1)),
            IsDecomposable B.tripleColoring ∧ HasPascalBounds B (d - (t + 1)) (t + 1) := by
          rw [← hchoose]
          exact classical_family (d - (t + 1)) (t + 1)
        obtain ⟨B, hBd, hB⟩ := hBex
        have hsize : (∑ j ∈ Finset.Icc L (t + 1), Nat.choose d j) =
            (∑ j ∈ Finset.Icc L t, Nat.choose d j) + Nat.choose d (t + 1) := by
          exact Finset.sum_Icc_succ_top (by omega) (fun j ↦ Nat.choose d j)
        rw [hsize]
        obtain ⟨P, hs, hL, hR⟩ := exists_deepComposition_coloring A B
        refine ⟨P, split_decomp hs (by simpa only [hL] using hAd)
          (by simpa only [hR] using hBd), ?_, ?_, ?_⟩
        · have h := hs.cap_chainSizeAtMost hL hR hAcap hB.1.1
          have heq : max (d - L + 1) (d - (t + 1) + 1 + 1) = d - L + 1 := by omega
          simpa only [heq] using h
        · simpa using hs.cup_chainSizeAtMost hL hR hAcup hB.1.2
        · apply strong_bound hs hL hR hAS (ac := t + 1) (bc := d - (t + 1) + 1)
          · intro r f hr
            have hh := hB.2 f hr
            have hm : max 1 ((d - (t + 1)) + (t + 1)) = d := by omega
            rw [hm] at hh
            omega
          · exact hAcup
          · exact hB.1.1
          · omega
  have construction : ∃ P : SweptConfiguration (decomposableThreshold a u k),
      IsDecomposable P.tripleColoring ∧
      ChainSizeAtMost P.tripleColoring Turn.right (a - 1) ∧
      ChainSizeAtMost P.tripleColoring Turn.left (u - 1) ∧
      StrongPolygonSizeAtMost P.tripleColoring (k - 1) := by
    by_cases hinactive : a + u ≤ k + 3
    · rw [decomposableThreshold_eq_choose ha hu hinactive]
      have hsize : a + u - 4 = (a - 2) + (u - 2) := by omega
      rw [hsize]
      obtain ⟨P, hPd, hP⟩ := classical_family (a - 2) (u - 2)
      refine ⟨P, hPd, ?_, ?_, ?_⟩
      · have heq : a - 2 + 1 = a - 1 := by omega
        simpa only [heq] using hP.1.1
      · have heq : u - 2 + 1 = u - 1 := by omega
        simpa only [heq] using hP.1.2
      · intro r f hr
        have hh := hP.2 f hr
        have hm : max 1 ((a - 2) + (u - 2)) ≤ k - 1 := by omega
        exact hh.trans hm
    · rw [decomposableThreshold_eq_window ha hu (by omega), decomposableBinomialWindow]
      obtain ⟨P, hPd, hPcap, hPcup, hPS⟩ :=
        windows (k - 2) (k - a) (u - 2) (by omega) (by omega) (by omega)
      refine ⟨P, hPd, ?_, ?_, ?_⟩
      · have heq : k - 2 - (k - a) + 1 = a - 1 := by omega
        simpa only [heq] using hPcap
      · have heq : u - 2 + 1 = u - 1 := by omega
        simpa only [heq] using hPcup
      · have heq : k - 2 + 1 = k - 1 := by omega
        simpa only [heq] using hPS
  obtain ⟨P, hPd, hPcap, hPcup, hPS⟩ := construction
  refine ⟨P.tripleColoring, hPd, hPd.isSweepRealizable, ?_, ?_, ?_⟩
  · intro T hT
    let e : Fin T.card ↪o Fin (decomposableThreshold a u k) := T.orderEmbOfFin rfl
    apply hPcup (f := e)
    refine ⟨e.strictMono, ?_⟩
    intro i j l hij hjl
    exact hT _ (T.orderEmbOfFin_mem rfl i) (T.orderEmbOfFin_mem rfl j)
      (T.orderEmbOfFin_mem rfl l)
  · intro T hT
    let e : Fin T.card ↪o Fin (decomposableThreshold a u k) := T.orderEmbOfFin rfl
    apply hPcap (f := e)
    refine ⟨e.strictMono, ?_⟩
    intro i j l hij hjl
    exact hT _ (T.orderEmbOfFin_mem rfl i) (T.orderEmbOfFin_mem rfl j)
      (T.orderEmbOfFin_mem rfl l)
  · rintro ⟨T, _, hcard, hT⟩
    let e : Fin k ↪o Fin (decomposableThreshold a u k) := T.orderEmbOfFin hcard
    have he : IsStrongPolygonOn P.tripleColoring e := by
      intro i j l r hij hjl hlr
      exact hT (e.strictMono hij) (e.strictMono hjl) (e.strictMono hlr)
        (T.orderEmbOfFin_mem hcard i) (T.orderEmbOfFin_mem hcard j)
        (T.orderEmbOfFin_mem hcard l) (T.orderEmbOfFin_mem hcard r)
    have hh := hPS e he
    omega


end ErdosSzekeres
