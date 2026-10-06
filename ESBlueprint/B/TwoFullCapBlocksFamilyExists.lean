import ESBlueprint.B.DeepSplitProfileGluingExists
import ESBlueprint.B.DecomposableColoringPushforwardExists
import ESBlueprint.B.DeepSplitFiniteEndpointConstraintsIff
import ESBlueprint.B.TwoFullCapBlocksRootNoninterval
import ErdosSzekeres.StructuralChargingNextState578SpanCounterexample
import ErdosSzekeres.DecomposableRealization

namespace ErdosSzekeres

/-- For every p at least two, construct a decomposable sweep-realizable coloring of two full ordered p-cap blocks with cap rank at most p, cup rank at most four and strong rank at most max(4,p); for p at least four every nonempty deep root has a four-cup and both interleaving gap witnesses.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.decomposable_coloring_pushforward_exists, ErdosSzekeres.deepSplit_profile_gluing_exists, ErdosSzekeres.deepSplit_finite_endpoint_constraints_iff, ErdosSzekeres.two_full_cap_blocks_root_noninterval, ErdosSzekeres.IsDecomposable.isSweepRealizable
@dangling-ok General attaining family needed for the persistent Q4 interval-root obstruction and the cup-four gate lower mechanism; induction bases are internal ingredients, with no standalone finite-instance target or closed context-bound equivalence. -/
theorem two_full_cap_blocks_family_exists (p : ℕ) (hp : 2 ≤ p) :
  ∃ χ : TripleColoring (2 * p),
    IsDecomposable χ ∧ IsSweepRealizable χ ∧
    IsCapSet χ (Finset.univ.filter fun i : Fin (2 * p) ↦ i.val < p) ∧
    IsCapSet χ (Finset.univ.filter fun i : Fin (2 * p) ↦ p ≤ i.val) ∧
    (∀ T : Finset (Fin (2 * p)), IsCupSet χ T → T.card ≤ 4) ∧
    (∀ T : Finset (Fin (2 * p)), IsCapSet χ T → T.card ≤ p) ∧
    (¬ ContainsStrongPolygonSet χ Finset.univ (max 4 p + 1)) ∧
    (4 ≤ p → ∀ lower upper : Finset (Fin (2 * p)),
      lower ∪ upper = Finset.univ → lower.Nonempty → upper.Nonempty →
      HasDeepBelowSplit χ lower upper →
      ContainsCupSet χ Finset.univ 4 ∧
      (∃ x y z : Fin (2 * p), x ∈ lower ∧ y ∈ upper ∧ z ∈ lower ∧ x < y ∧ y < z) ∧
      (∃ x y z : Fin (2 * p), x ∈ upper ∧ y ∈ lower ∧ z ∈ upper ∧ x < y ∧ y < z)) := by
  classical
  have cup_agree {n : ℕ} {χ ψ : TripleColoring n}
      {S T : Finset (Fin n)} (hTS : T ⊆ S) (h : χ.AgreeOnTriples ψ S) :
      IsCupSet χ T ↔ IsCupSet ψ T := by
    constructor <;> intro hT t hi hj hk
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).symm.trans (hT t hi hj hk)
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).trans (hT t hi hj hk)
  have cap_agree {n : ℕ} {χ ψ : TripleColoring n}
      {S T : Finset (Fin n)} (hTS : T ⊆ S) (h : χ.AgreeOnTriples ψ S) :
      IsCapSet χ T ↔ IsCapSet ψ T := by
    constructor <;> intro hT t hi hj hk
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).symm.trans (hT t hi hj hk)
    · exact (h t (hTS hi) (hTS hj) (hTS hk)).trans (hT t hi hj hk)
  have noStrong_card {n s : ℕ} (χ : TripleColoring n) (S : Finset (Fin n))
      (hS : S.card ≤ s) : ¬ ContainsStrongPolygonSet χ S (s + 1) := by
    rintro ⟨T, hTS, hcard, _⟩
    have := Finset.card_le_card hTS
    omega
  have noStrong_larger {n a b : ℕ} {χ : TripleColoring n} {S : Finset (Fin n)}
      (hno : ¬ ContainsStrongPolygonSet χ S (a + 1)) (hab : a ≤ b) :
      ¬ ContainsStrongPolygonSet χ S (b + 1) := by
    rintro ⟨T, hTS, hcard, hstrong⟩
    obtain ⟨D, hDT, hDcard⟩ := Finset.exists_subset_card_eq
      (show a + 1 ≤ T.card by omega)
    exact hno ⟨D, hDT.trans hTS, hDcard,
      FinsetPolygon.IsStrongPolygonSet.mono hstrong hDT⟩
  have constant_cap_decomp {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
      IsDecomposableOn (fun _ ↦ Turn.right) S := by
    have hcup : IsCupSet (fun _ : OrderedTriple n ↦ Turn.left) S := by
      intro t hi hj hk
      rfl
    simpa [TripleColoring.dual, Turn.dual] using
      (FinsetPolygon.IsCupSet.isDecomposableOn_of_nonempty hcup hS).dual
  have constant_cap_cup_bound {n : ℕ} (T : Finset (Fin n))
      (hT : IsCupSet (fun _ ↦ Turn.right) T) : T.card ≤ 2 := by
    have hcap : IsCapSet (fun _ : OrderedTriple n ↦ Turn.right) T := by
      intro t hi hj hk
      rfl
    simpa using inter_card_le_two_of_cup_cap hT hcap
  have card_split {n : ℕ} (T L U : Finset (Fin n)) (hT : T ⊆ L ∪ U) :
      T.card ≤ (T ∩ L).card + (T ∩ U).card := by
    have heq : (T ∩ L) ∪ (T ∩ U) = T := by
      ext z
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
      · intro hz
        rcases Finset.mem_union.mp (hT hz) with hL | hU
        · exact Or.inl ⟨hz, hL⟩
        · exact Or.inr ⟨hz, hU⟩
    simpa only [heq] using Finset.card_union_le (T ∩ L) (T ∩ U)
  have glue {n s : ℕ} (ψL ψU : TripleColoring n) (L U : Finset (Fin n))
      (hdis : Disjoint L U) (hLd : IsDecomposableOn ψL L)
      (hUd : IsDecomposableOn ψU U)
      (hnoL : ¬ ContainsStrongPolygonSet ψL L (s + 1))
      (hnoU : ¬ ContainsStrongPolygonSet ψU U (s + 1))
      (hc : ∀ C D : Finset (Fin n), C ⊆ L → D ⊆ U →
        IsCupSet ψL C → IsCapSet ψU D → C.card + D.card ≤ s) :
      ∃ χ : TripleColoring n, χ.AgreeOnTriples ψL L ∧ χ.AgreeOnTriples ψU U ∧
        HasDeepBelowSplit χ L U ∧ IsDecomposableOn χ (L ∪ U) ∧
        ¬ ContainsStrongPolygonSet χ (L ∪ U) (s + 1) := by
    obtain ⟨χ, hL, hU, hd, hdec, hno, _⟩ :=
      deepSplit_profile_gluing_exists ψL ψU hdis hLd hUd hnoL hnoU
        (fun _ ↦ True) (fun _ ↦ True)
        (by intros; trivial) (by intros; trivial)
        (by intros; trivial) (by intros; trivial) hc
    exact ⟨χ, hL, hU, hd, hdec, hno⟩
  have rank_bounds {n a b c d : ℕ} {χ : TripleColoring n}
      {L U : Finset (Fin n)} (hd : HasDeepBelowSplit χ L U)
      (hCL : ∀ T, T ⊆ L → IsCupSet χ T → T.card ≤ a)
      (hCU : ∀ T, T ⊆ U → IsCupSet χ T → T.card ≤ b)
      (hAL : ∀ T, T ⊆ L → IsCapSet χ T → T.card ≤ c)
      (hAU : ∀ T, T ⊆ U → IsCapSet χ T → T.card ≤ d) :
      (∀ T, T ⊆ L ∪ U → IsCupSet χ T → T.card ≤ max b (a + 2)) ∧
      (∀ T, T ⊆ L ∪ U → IsCapSet χ T → T.card ≤ max c (d + 2)) := by
    have hcupB := Nat.le_max_left b (a + 2)
    have hcupA := Nat.le_max_right b (a + 2)
    have hcapC := Nat.le_max_left c (d + 2)
    have hcapD := Nat.le_max_right c (d + 2)
    apply (deepSplit_finite_endpoint_constraints_iff hd
      (fun T ↦ T.card ≤ max b (a + 2))
      (fun T ↦ T.card ≤ max c (d + 2))).mpr
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro T hTL hT
      have := hCL T hTL hT
      omega
    · intro T hTU hT
      have := hCU T hTU hT
      omega
    · intro C hCL' hC q _ _
      have := hCL C hCL' hC
      have := Finset.card_insert_le q C
      omega
    · intro C hCL' hC x y _ _ _ _ _
      have := hCL C hCL' hC
      have := Finset.card_insert_le y C
      have := Finset.card_insert_le x (insert y C)
      omega
    · intro T hTU hT
      have := hAU T hTU hT
      omega
    · intro T hTL hT
      have := hAL T hTL hT
      omega
    · intro C hCU' hC q _ _
      have := hAU C hCU' hC
      have := Finset.card_insert_le q C
      omega
    · intro C hCU' hC x y _ _ _ _ _
      have := hAU C hCU' hC
      have := Finset.card_insert_le y C
      have := Finset.card_insert_le x (insert y C)
      omega
  have family : ∀ q : ℕ, 2 ≤ q → ∃ χ : TripleColoring (2 * q),
      IsDecomposable χ ∧
      IsCapSet χ (Finset.univ.filter fun i : Fin (2 * q) ↦ i.val < q) ∧
      IsCapSet χ (Finset.univ.filter fun i : Fin (2 * q) ↦ q ≤ i.val) ∧
      (∀ T : Finset (Fin (2 * q)), IsCupSet χ T → T.card ≤ 4) ∧
      (∀ T : Finset (Fin (2 * q)), IsCapSet χ T → T.card ≤ q) ∧
      ¬ ContainsStrongPolygonSet χ Finset.univ (max 4 q + 1) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hq
      by_cases htwo : q = 2
      · subst q
        let χ : TripleColoring 4 := fun _ ↦ Turn.left
        have hcup : IsCupSet χ Finset.univ := by intro t hi hj hk; rfl
        refine ⟨χ, FinsetPolygon.IsCupSet.isDecomposableOn_of_nonempty
          hcup (by simp), ?_, ?_, ?_, ?_, ?_⟩
        · intro t hi hj hk
          have hi' : t.i.val < 2 := (Finset.mem_filter.mp hi).2
          have hk' : t.k.val < 2 := (Finset.mem_filter.mp hk).2
          have hij := t.hij
          have hjk := t.hjk
          change t.i.val < t.j.val at hij
          change t.j.val < t.k.val at hjk
          omega
        · intro t hi hj hk
          have hi' : 2 ≤ t.i.val := (Finset.mem_filter.mp hi).2
          have hk' := t.k.isLt
          have hij := t.hij
          have hjk := t.hjk
          change t.i.val < t.j.val at hij
          change t.j.val < t.k.val at hjk
          omega
        · intro T _
          simpa using (Finset.card_le_univ T : T.card ≤ Fintype.card (Fin 4))
        · intro T hT
          simpa using inter_card_le_two_of_cup_cap hcup hT
        · exact noStrong_card χ Finset.univ (by simp)
      by_cases hthree : q = 3
      · subst q
        let A : Finset (Fin 6) := {0, 1, 2}
        let B : Finset (Fin 6) := {3, 5}
        let L := A ∪ B
        let V : Finset (Fin 6) := {4}
        let ψ : TripleColoring 6 := fun _ ↦ Turn.right
        have hAcard : A.card = 3 := by decide
        have hBcard : B.card = 2 := by decide
        have hVcard : V.card = 1 := by decide
        have hAval (z : Fin 6) (hz : z ∈ A) : z.val ≤ 2 := by
          simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> norm_num
        have hBval (z : Fin 6) (hz : z ∈ B) : 3 ≤ z.val := by
          simp only [B, Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> norm_num
        obtain ⟨inner, hIA, hIB, hiDeep, hiDec, hiNo⟩ :=
          glue (s := 4) ψ ψ A B (by decide)
            (constant_cap_decomp A (by decide))
            (constant_cap_decomp B (by decide))
            (noStrong_card ψ A (by omega)) (noStrong_card ψ B (by omega))
            (by
              intro C D _ hDB hC _
              have hCcard := constant_cap_cup_bound C hC
              have hDcard := Finset.card_le_card hDB
              omega)
        have hiBounds :
            (∀ T, T ⊆ L → IsCupSet inner T → T.card ≤ 3) ∧
            (∀ T, T ⊆ L → IsCapSet inner T → T.card ≤ 3) := by
          apply (deepSplit_finite_endpoint_constraints_iff hiDeep
            (fun T ↦ T.card ≤ 3) (fun T ↦ T.card ≤ 3)).mpr
          refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
          · intro T hTA hT
            have := constant_cap_cup_bound T ((cup_agree hTA hIA).mp hT)
            omega
          · intro T hTB _
            have := Finset.card_le_card hTB
            omega
          · intro C hCA hC x _ _
            have := constant_cap_cup_bound C ((cup_agree hCA hIA).mp hC)
            have := Finset.card_insert_le x C
            omega
          · intro C hCA _ x y hx _ _ hxl _
            have hCE : C = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro z hz
              have := hAval z (hCA hz)
              have := hBval x hx
              have hlt := hxl z hz
              change x.val < z.val at hlt
              omega
            have := Finset.card_insert_le y C
            have := Finset.card_insert_le x (insert y C)
            have hzero : C.card = 0 := by simp [hCE]
            omega
          · intro T hTB _
            have := Finset.card_le_card hTB
            omega
          · intro T hTA _
            have := Finset.card_le_card hTA
            omega
          · intro C hCB _ x _ _
            have := Finset.card_le_card hCB
            have := Finset.card_insert_le x C
            omega
          · intro C hCB _ x y _ hy _ _ hry
            have hCE : C = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro z hz
              have := hBval z (hCB hz)
              have := hAval y hy
              have hlt := hry z hz
              change z.val < y.val at hlt
              omega
            have := Finset.card_insert_le y C
            have := Finset.card_insert_le x (insert y C)
            have hzero : C.card = 0 := by simp [hCE]
            omega
        have hLV : L ∪ V = Finset.univ := by decide
        obtain ⟨χ, hXL, hXV, hd, hdec, hno⟩ :=
          glue (s := 4) inner ψ L V (by decide) hiDec (.singleton 4) hiNo
            (noStrong_card ψ V (by omega))
            (by
              intro C D hCL hDV hC _
              have := hiBounds.1 C hCL hC
              have := Finset.card_le_card hDV
              omega)
        have hLcup (T : Finset (Fin 6)) (hTL : T ⊆ L) (hT : IsCupSet χ T) :
            T.card ≤ 3 := hiBounds.1 T hTL ((cup_agree hTL hXL).mp hT)
        have hLcap (T : Finset (Fin 6)) (hTL : T ⊆ L) (hT : IsCapSet χ T) :
            T.card ≤ 3 := hiBounds.2 T hTL ((cap_agree hTL hXL).mp hT)
        have hVbound (T : Finset (Fin 6)) (hTV : T ⊆ V) : T.card ≤ 1 := by
          have := Finset.card_le_card hTV
          omega
        have hRbounds := rank_bounds hd hLcup (fun T hTV _ ↦ hVbound T hTV)
          hLcap (fun T hTV _ ↦ hVbound T hTV)
        have hcapA : IsCapSet χ A :=
          (cap_agree (Finset.subset_union_left : A ⊆ L) hXL).mpr
            ((cap_agree Finset.Subset.rfl hIA).mpr (by intro t hi hj hk; rfl))
        have hcapV : IsCapSet χ V :=
          (cap_agree Finset.Subset.rfl hXV).mpr (by intro t hi hj hk; rfl)
        have hcapLast : IsCapSet χ (insert 3 (insert 5 V)) :=
          (deepSplit_two_endpoint_extensions hd).2 V Finset.Subset.rfl hcapV
            3 5 (by decide) (by decide) (by decide)
            (by intro z hz; simp only [V, Finset.mem_singleton] at hz; subst z; decide)
            (by intro z hz; simp only [V, Finset.mem_singleton] at hz; subst z; decide)
        refine ⟨χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [IsDecomposable, hLV] using hdec
        · have heq : (Finset.univ.filter fun i : Fin 6 ↦ i.val < 3) = A := by decide
          rw [heq]
          exact hcapA
        · have heq : (Finset.univ.filter fun i : Fin 6 ↦ 3 ≤ i.val) =
              insert 3 (insert 5 V) := by decide
          rw [heq]
          exact hcapLast
        · intro T hT
          have hTsub : T ⊆ L ∪ V := by rw [hLV]; exact Finset.subset_univ T
          have hsize := card_split T L V hTsub
          have hLC := hLcup (T ∩ L) Finset.inter_subset_right
            (FinsetPolygon.IsCupSet.mono hT Finset.inter_subset_left)
          have hVC := hVbound (T ∩ V) Finset.inter_subset_right
          omega
        · intro T hT
          have hTsub : T ⊆ L ∪ V := by rw [hLV]; exact Finset.subset_univ T
          simpa using hRbounds.2 T hTsub hT
        · simpa only [hLV] using hno
      have hq4 : 4 ≤ q := by omega
      let r := q - 2
      have hr2 : 2 ≤ r := by dsimp [r]; omega
      have hrq : r < q := by dsimp [r]; omega
      obtain ⟨old, oldDec, oldFirst, oldLast, oldCup, oldCap, oldNo⟩ := ih r hrq hr2
      let f : Fin (2 * r) ↪o Fin (2 * q) := OrderEmbedding.ofStrictMono
        (fun i ↦ (⟨if i.val < r then i.val + 1 else i.val + 3, by
          split <;> dsimp [r] at * <;> omega⟩ : Fin (2 * q)))
        (by
          intro i j hij
          change i.val < j.val at hij
          change (if i.val < r then i.val + 1 else i.val + 3) <
            (if j.val < r then j.val + 1 else j.val + 3)
          split <;> split <;> omega)
      let a : Fin (2 * q) := ⟨0, by omega⟩
      let b : Fin (2 * q) := ⟨q - 1, by omega⟩
      let c : Fin (2 * q) := ⟨q, by omega⟩
      let d : Fin (2 * q) := ⟨2 * q - 1, by omega⟩
      let L : Finset (Fin (2 * q)) := {a, b, c, d}
      let U : Finset (Fin (2 * q)) := Finset.univ.image f
      have hUmem (z : Fin (2 * q)) : z ∈ U ↔
          (0 < z.val ∧ z.val < q - 1) ∨ (q < z.val ∧ z.val < 2 * q - 1) := by
        constructor
        · intro hz
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
          by_cases hi : i.val < r
          · left
            simp [f, hi]
            dsimp [r] at hi
            omega
          · right
            simp [f, hi]
            have := i.isLt
            dsimp [r] at *
            omega
        · rintro (⟨hz0, hzq⟩ | ⟨hzq, hz2q⟩)
          · let i : Fin (2 * r) := ⟨z.val - 1, by dsimp [r]; omega⟩
            refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
            apply Fin.ext
            have hi : i.val < r := by dsimp [i, r]; omega
            simp [f, hi, i]
            omega
          · let i : Fin (2 * r) := ⟨z.val - 3, by dsimp [r]; omega⟩
            refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
            apply Fin.ext
            have hi : ¬ i.val < r := by dsimp [i, r]; omega
            simp [f, hi, i]
            omega
      have hdis : Disjoint L U := by
        rw [Finset.disjoint_left]
        intro z hzL hzU
        have hz := (hUmem z).mp hzU
        simp only [L, Finset.mem_insert, Finset.mem_singleton] at hzL
        rcases hzL with rfl | rfl | rfl | rfl <;> dsimp [a, b, c, d] at hz <;> omega
      have hLU : L ∪ U = Finset.univ := by
        ext z
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_cases hzL : z ∈ L
        · exact Or.inl hzL
        · right
          apply (hUmem z).mpr
          have hneA : z.val ≠ 0 := by intro h; apply hzL; simp [L, a, Fin.ext_iff, h]
          have hneB : z.val ≠ q - 1 := by intro h; apply hzL; simp [L, b, Fin.ext_iff, h]
          have hneC : z.val ≠ q := by intro h; apply hzL; simp [L, c, Fin.ext_iff, h]
          have hneD : z.val ≠ 2 * q - 1 := by intro h; apply hzL; simp [L, d, Fin.ext_iff, h]
          have := z.isLt
          omega
      have hLcard : L.card = 4 := by
        have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
        have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a, c] at this; omega
        have had : a ≠ d := by intro h; have := congrArg Fin.val h; dsimp [a, d] at this; omega
        have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b, c] at this; omega
        have hbd : b ≠ d := by intro h; have := congrArg Fin.val h; dsimp [b, d] at this; omega
        have hcd : c ≠ d := by intro h; have := congrArg Fin.val h; dsimp [c, d] at this; omega
        simp [L, hab, hac, had, hbc, hbd, hcd]
      obtain ⟨σ, hrestrict, hDecImage, hCupImage, hCapImage, hStrongImage, hCardImage⟩ :=
        decomposable_coloring_pushforward_exists old f
      have hUcup (T : Finset (Fin (2 * q))) (hTU : T ⊆ U) (hT : IsCupSet σ T) :
          T.card ≤ 4 := by
        obtain ⟨S, _, hST⟩ := Finset.subset_image_iff.mp hTU
        have hScup : IsCupSet old S := (hCupImage S).mpr (by simpa [hST] using hT)
        have := oldCup S hScup
        rw [← hST, hCardImage]
        exact this
      have hUcap (T : Finset (Fin (2 * q))) (hTU : T ⊆ U) (hT : IsCapSet σ T) :
          T.card ≤ r := by
        obtain ⟨S, _, hST⟩ := Finset.subset_image_iff.mp hTU
        have hScap : IsCapSet old S := (hCapImage S).mpr (by simpa [hST] using hT)
        have := oldCap S hScap
        rw [← hST, hCardImage]
        exact this
      have hnoU : ¬ ContainsStrongPolygonSet σ U (q + 1) := by
        intro hno
        have hbound : max 4 r ≤ q := max_le hq4 (by dsimp [r]; omega)
        exact noStrong_larger oldNo hbound ((hStrongImage Finset.univ (q + 1)).mpr hno)
      let ψ : TripleColoring (2 * q) := fun _ ↦ Turn.right
      obtain ⟨χ, hXL, hXU, hd, hdec, hno⟩ :=
        glue (s := q) ψ σ L U hdis
          (constant_cap_decomp L ⟨a, by simp [L]⟩)
          (hDecImage Finset.univ oldDec)
          (noStrong_card ψ L (by omega)) hnoU
          (by
            intro C D _ hDU hC hD
            have := constant_cap_cup_bound C hC
            have := hUcap D hDU hD
            dsimp [r] at *
            omega)
      have hCL (T : Finset (Fin (2 * q))) (hTL : T ⊆ L) (hT : IsCupSet χ T) :
          T.card ≤ 2 := constant_cap_cup_bound T ((cup_agree hTL hXL).mp hT)
      have hAL (T : Finset (Fin (2 * q))) (hTL : T ⊆ L) (_ : IsCapSet χ T) :
          T.card ≤ 4 := by have := Finset.card_le_card hTL; omega
      have hbounds := rank_bounds hd hCL
        (fun T hTU hT ↦ hUcup T hTU ((cup_agree hTU hXU).mp hT)) hAL
        (fun T hTU hT ↦ hUcap T hTU ((cap_agree hTU hXU).mp hT))
      let S0 := Finset.univ.filter fun i : Fin (2 * r) ↦ i.val < r
      let S1 := Finset.univ.filter fun i : Fin (2 * r) ↦ r ≤ i.val
      let C0 := S0.image f
      let C1 := S1.image f
      have hC0U : C0 ⊆ U := Finset.image_mono f (Finset.filter_subset _ _)
      have hC1U : C1 ⊆ U := Finset.image_mono f (Finset.filter_subset _ _)
      have hC0mem (z : Fin (2 * q)) : z ∈ C0 ↔ 0 < z.val ∧ z.val < q - 1 := by
        constructor
        · intro hz
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
          have hi' : i.val < r := (Finset.mem_filter.mp hi).2
          simp [f, hi']
          dsimp [r] at hi'
          omega
        · rintro ⟨hz0, hzq⟩
          let i : Fin (2 * r) := ⟨z.val - 1, by dsimp [r]; omega⟩
          have hi : i.val < r := by dsimp [i, r]; omega
          refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
          apply Fin.ext
          simp [f, hi, i]
          omega
      have hC1mem (z : Fin (2 * q)) : z ∈ C1 ↔ q < z.val ∧ z.val < 2 * q - 1 := by
        constructor
        · intro hz
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
          have hi' : r ≤ i.val := (Finset.mem_filter.mp hi).2
          have hi'' : ¬ i.val < r := by omega
          simp [f, hi'']
          have := i.isLt
          dsimp [r] at *
          omega
        · rintro ⟨hzq, hz2q⟩
          let i : Fin (2 * r) := ⟨z.val - 3, by dsimp [r]; omega⟩
          have hi : r ≤ i.val := by dsimp [i, r]; omega
          have hi' : ¬ i.val < r := by omega
          refine Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
          apply Fin.ext
          simp [f, hi', i]
          omega
      have hcap0 : IsCapSet χ C0 :=
        (cap_agree hC0U hXU).mpr ((hCapImage S0).mp oldFirst)
      have hcap1 : IsCapSet χ C1 :=
        (cap_agree hC1U hXU).mpr ((hCapImage S1).mp oldLast)
      have hfirst : IsCapSet χ (insert a (insert b C0)) :=
        (deepSplit_two_endpoint_extensions hd).2 C0 hC0U hcap0 a b
          (by simp [L]) (by simp [L]) (by change 0 < q - 1; omega)
          (by intro z hz; exact (hC0mem z).mp hz |>.1)
          (by intro z hz; exact (hC0mem z).mp hz |>.2)
      have hlast : IsCapSet χ (insert c (insert d C1)) :=
        (deepSplit_two_endpoint_extensions hd).2 C1 hC1U hcap1 c d
          (by simp [L]) (by simp [L]) (by change q < 2 * q - 1; omega)
          (by intro z hz; exact (hC1mem z).mp hz |>.1)
          (by intro z hz; exact (hC1mem z).mp hz |>.2)
      have hfirstSet : (Finset.univ.filter fun i : Fin (2 * q) ↦ i.val < q) =
          insert a (insert b C0) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        rw [hC0mem]
        simp only [Fin.ext_iff]
        dsimp [a, b]
        omega
      have hlastSet : (Finset.univ.filter fun i : Fin (2 * q) ↦ q ≤ i.val) =
          insert c (insert d C1) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        rw [hC1mem]
        simp only [Fin.ext_iff]
        dsimp [c, d]
        have := z.isLt
        omega
      refine ⟨χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [IsDecomposable, hLU] using hdec
      · simpa only [hfirstSet] using hfirst
      · simpa only [hlastSet] using hlast
      · intro T hT
        have hTsub : T ⊆ L ∪ U := by rw [hLU]; exact Finset.subset_univ T
        simpa using hbounds.1 T hTsub hT
      · intro T hT
        have hTsub : T ⊆ L ∪ U := by rw [hLU]; exact Finset.subset_univ T
        have := hbounds.2 T hTsub hT
        dsimp [r] at this
        omega
      · simpa only [hLU, Nat.max_eq_right hq4] using hno
  obtain ⟨χ, hdec, hfirst, hlast, hcup, hcap, hno⟩ := family p hp
  let Z0 := Finset.univ.filter fun i : Fin (2 * p) ↦ i.val < p
  let Z1 := Finset.univ.filter fun i : Fin (2 * p) ↦ p ≤ i.val
  have hdisZ : Disjoint Z0 Z1 := by
    rw [Finset.disjoint_left]
    intro z hz0 hz1
    have := (Finset.mem_filter.mp hz0).2
    have := (Finset.mem_filter.mp hz1).2
    omega
  have hcoverZ : Z0 ∪ Z1 = Finset.univ := by
    ext z
    simp only [Z0, Z1, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    omega
  let g : Fin p ↪o Fin (2 * p) := OrderEmbedding.ofStrictMono
    (fun i ↦ (⟨i.val, by omega⟩ : Fin (2 * p))) (by intro i j hij; exact hij)
  have himageG : Finset.univ.image g = Z0 := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
    · intro hz
      have hz' : z.val < p := (Finset.mem_filter.mp hz).2
      exact Finset.mem_image.mpr ⟨⟨z.val, hz'⟩, Finset.mem_univ _, rfl⟩
  have hcard0 : Z0.card = p := by
    rw [← himageG, Finset.card_image_of_injective _ g.injective]
    simp
  have hcard1 : Z1.card = p := by
    have hsum := Finset.card_union_of_disjoint hdisZ
    rw [hcoverZ, hcard0] at hsum
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  refine ⟨χ, hdec, hdec.isSweepRealizable, hfirst, hlast, hcup, hcap, hno, ?_⟩
  intro hp4 lower upper hcover hLower hUpper hd
  have hnoCap : ¬ ContainsCapSet χ (lower ∪ upper) (p + 1) := by
    rintro ⟨T, _, hTcard, hT⟩
    have := hcap T hT
    omega
  have hnoStrong : ¬ ContainsStrongPolygonSet χ (lower ∪ upper) (p + 1) := by
    simpa only [hcover, Nat.max_eq_right hp4] using hno
  have hsep : ∀ x ∈ Z0, ∀ y ∈ Z1, x < y := by
    intro x hx y hy
    have := (Finset.mem_filter.mp hx).2
    have := (Finset.mem_filter.mp hy).2
    change x.val < y.val
    omega
  have hroot := two_full_cap_blocks_root_noninterval hp4 hd hLower hUpper hdisZ
    (hcoverZ.trans hcover.symm) hsep hfirst hlast hcard0 hcard1 hnoCap hnoStrong
  simpa only [hcover] using hroot


end ErdosSzekeres
