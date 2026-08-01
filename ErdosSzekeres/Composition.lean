import ErdosSzekeres.SmallCases

/-!
# Deep splits of sweep colorings

A deep split is the combinatorial signature of placing a left block deep below
a right block. Mixed triples with two left vertices turn left, while mixed
triples with two right vertices turn right. These are the local rules used by
the Erdős--Szekeres lower constructions.
-/

namespace ErdosSzekeres

noncomputable section

theorem exists_strictUpperBound_of_finite {ι : Type*} [Finite ι]
    (f : ι → ℝ) : ∃ M : ℝ, ∀ i, f i < M := by
  refine ⟨sSup (Set.range f) + 1, ?_⟩
  intro i
  have hi : f i ≤ sSup (Set.range f) :=
    le_csSup (Finite.bddAbove_range f) ⟨i, rfl⟩
  linarith

def translatePoint (x y : ℝ) (p : Point 2) : Point 2 :=
  ![p 0 + x, p 1 + y]

@[simp] theorem translatePoint_zero (x y : ℝ) (p : Point 2) :
    translatePoint x y p 0 = p 0 + x := by simp [translatePoint]

@[simp] theorem translatePoint_one (x y : ℝ) (p : Point 2) :
    translatePoint x y p 1 = p 1 + y := by simp [translatePoint]

@[simp] theorem orientation_translatePoint (x y : ℝ) (a b c : Point 2) :
    orientation (translatePoint x y a) (translatePoint x y b)
      (translatePoint x y c) = orientation a b c := by
  simp [orientation]

theorem orientation_translatePoint_right (x y : ℝ) (a b c : Point 2) :
    orientation a b (translatePoint x y c) =
      orientation a b (translatePoint x 0 c) + (b 0 - a 0) * y := by
  simp [orientation]
  ring

theorem orientation_translatePoint_right_right (x y : ℝ) (a b c : Point 2) :
    orientation a (translatePoint x y b) (translatePoint x y c) =
      orientation a (translatePoint x 0 b) (translatePoint x 0 c) -
        (c 0 - b 0) * y := by
  simp [orientation]
  ring

theorem exists_deepSeparationParameters {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) :
    ∃ x y : ℝ,
      (∀ i j, A.point i 0 < translatePoint x y (B.point j) 0) ∧
      (∀ (i j : Fin m) (k : Fin n), i < j →
        0 < orientation (A.point i) (A.point j) (translatePoint x y (B.point k))) ∧
      (∀ (i : Fin m) (j k : Fin n), j < k →
        orientation (A.point i) (translatePoint x y (B.point j))
          (translatePoint x y (B.point k)) < 0) := by
  classical
  obtain ⟨x, hx⟩ := exists_strictUpperBound_of_finite
    (fun q : Fin m × Fin n => A.point q.1 0 - B.point q.2 0)
  obtain ⟨y₁, hy₁⟩ := exists_strictUpperBound_of_finite
    (fun q : (Fin m × Fin m) × Fin n =>
      if q.1.1 < q.1.2 then
        -orientation (A.point q.1.1) (A.point q.1.2)
            (translatePoint x 0 (B.point q.2)) /
          (A.point q.1.2 0 - A.point q.1.1 0)
      else 0)
  obtain ⟨y₂, hy₂⟩ := exists_strictUpperBound_of_finite
    (fun q : Fin m × (Fin n × Fin n) =>
      if q.2.1 < q.2.2 then
        orientation (A.point q.1) (translatePoint x 0 (B.point q.2.1))
            (translatePoint x 0 (B.point q.2.2)) /
          (B.point q.2.2 0 - B.point q.2.1 0)
      else 0)
  let y := max y₁ y₂
  refine ⟨x, y, ?_, ?_, ?_⟩
  · intro i j
    have h := hx (i, j)
    simp only [translatePoint_zero]
    linarith
  · intro i j k hij
    have hdx : 0 < A.point j 0 - A.point i 0 :=
      sub_pos.mpr (A.sweep_strictMono hij)
    have hbound := hy₁ ((i, j), k)
    simp [hij] at hbound
    have hbound' :
        -orientation (A.point i) (A.point j) (translatePoint x 0 (B.point k)) <
          y * (A.point j 0 - A.point i 0) := by
      have := (div_lt_iff₀ hdx).mp hbound
      dsimp [y]
      nlinarith [le_max_left y₁ y₂]
    rw [orientation_translatePoint_right]
    nlinarith
  · intro i j k hjk
    have hdx : 0 < B.point k 0 - B.point j 0 :=
      sub_pos.mpr (B.sweep_strictMono hjk)
    have hbound := hy₂ (i, (j, k))
    simp [hjk] at hbound
    have hbound' :
        orientation (A.point i) (translatePoint x 0 (B.point j))
            (translatePoint x 0 (B.point k)) <
          y * (B.point k 0 - B.point j 0) := by
      have := (div_lt_iff₀ hdx).mp hbound
      dsimp [y]
      nlinarith [le_max_right y₁ y₂]
    rw [orientation_translatePoint_right_right]
    nlinarith

def deepComposePoint {m n : ℕ} (A : SweptConfiguration m)
    (B : SweptConfiguration n) (x y : ℝ) : Fin (m + n) → Point 2 :=
  Fin.append A.point (fun j => translatePoint x y (B.point j))

theorem generalPosition_of_ordered {n : ℕ} (p : Fin n → Point 2)
    (hordered : ∀ (i j k : Fin n), i < j → j < k →
      orientation (p i) (p j) (p k) ≠ 0) :
    ∀ ⦃i j k : Fin n⦄, i ≠ j → i ≠ k → j ≠ k →
      orientation (p i) (p j) (p k) ≠ 0 := by
  intro i j k hij hik hjk
  rcases lt_or_gt_of_ne hij with hij' | hji
  · rcases lt_or_gt_of_ne hjk with hjk' | hkj
    · exact hordered i j k hij' hjk'
    · rcases lt_or_gt_of_ne hik with hik' | hki
      · have h := hordered i k j hik' hkj
        intro hz
        apply h
        simp only [orientation] at *
        nlinarith
      · have h := hordered k i j hki hij'
        intro hz
        apply h
        simp only [orientation] at *
        nlinarith
  · rcases lt_or_gt_of_ne hik with hik' | hki
    · have h := hordered j i k hji hik'
      intro hz
      apply h
      simp only [orientation] at *
      nlinarith
    · rcases lt_or_gt_of_ne hjk with hjk' | hkj
      · have h := hordered j k i hjk' hki
        intro hz
        apply h
        simp only [orientation] at *
        nlinarith
      · have h := hordered k j i hkj hji
        intro hz
        apply h
        simp only [orientation] at *
        nlinarith

theorem deepComposePoint_generalPosition {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) (x y : ℝ)
    (hllr : ∀ (i j : Fin m) (k : Fin n), i < j →
      0 < orientation (A.point i) (A.point j) (translatePoint x y (B.point k)))
    (hlrr : ∀ (i : Fin m) (j k : Fin n), j < k →
      orientation (A.point i) (translatePoint x y (B.point j))
        (translatePoint x y (B.point k)) < 0) :
    ∀ ⦃i j k : Fin (m + n)⦄,
      i ≠ j → i ≠ k → j ≠ k →
        orientation (deepComposePoint A B x y i)
          (deepComposePoint A B x y j) (deepComposePoint A B x y k) ≠ 0 := by
  apply generalPosition_of_ordered
  intro i j k hij hjk
  have hijv : i.val < j.val := hij
  have hjkv : j.val < k.val := hjk
  have hkbound : k.val < m + n := k.isLt
  by_cases hk : k.val < m
  · have hj : j.val < m := by omega
    have hi : i.val < m := by omega
    let ai : Fin m := ⟨i.val, hi⟩
    let aj : Fin m := ⟨j.val, hj⟩
    let ak : Fin m := ⟨k.val, hk⟩
    have hai : Fin.castAdd n ai = i := by ext; rfl
    have haj : Fin.castAdd n aj = j := by ext; rfl
    have hak : Fin.castAdd n ak = k := by ext; rfl
    rw [← hai, ← haj, ← hak]
    simpa [deepComposePoint] using A.generalPosition
      (ne_of_lt (show ai < aj by exact hij))
      (ne_of_lt (show ai < ak by exact hij.trans hjk))
      (ne_of_lt (show aj < ak by exact hjk))
  · have hkm : m ≤ k.val := by omega
    let bk : Fin n := ⟨k.val - m, by omega⟩
    have hbk : Fin.natAdd m bk = k := by ext; simp [bk]; omega
    by_cases hj : j.val < m
    · have hi : i.val < m := by omega
      let ai : Fin m := ⟨i.val, hi⟩
      let aj : Fin m := ⟨j.val, hj⟩
      have haiaj : ai < aj := by change i.val < j.val; exact hij
      have hai : Fin.castAdd n ai = i := by ext; rfl
      have haj : Fin.castAdd n aj = j := by ext; rfl
      have hpos := hllr ai aj bk haiaj
      rw [← hai, ← haj, ← hbk]
      exact ne_of_gt (by simpa [deepComposePoint] using hpos)
    · have hjm : m ≤ j.val := by omega
      let bj : Fin n := ⟨j.val - m, by omega⟩
      have hbj : Fin.natAdd m bj = j := by ext; simp [bj]; omega
      have hbjbk : bj < bk := by change j.val - m < k.val - m; omega
      by_cases hi : i.val < m
      · let ai : Fin m := ⟨i.val, hi⟩
        have hai : Fin.castAdd n ai = i := by ext; rfl
        rw [← hai, ← hbj, ← hbk]
        exact ne_of_lt (by simpa [deepComposePoint] using hlrr ai bj bk hbjbk)
      · have him : m ≤ i.val := by omega
        let bi : Fin n := ⟨i.val - m, by omega⟩
        have hbi : Fin.natAdd m bi = i := by ext; simp [bi]; omega
        have hbibj : bi < bj := by change i.val - m < j.val - m; omega
        rw [← hbi, ← hbj, ← hbk]
        simpa [deepComposePoint] using B.generalPosition
          (ne_of_lt hbibj) (ne_of_lt (hbibj.trans hbjbk)) (ne_of_lt hbjbk)

namespace SweptConfiguration

def deepCompose {m n : ℕ} (A : SweptConfiguration m)
    (B : SweptConfiguration n) (x y : ℝ)
    (hx : ∀ i j, A.point i 0 < translatePoint x y (B.point j) 0)
    (hgeneral : ∀ ⦃i j k : Fin (m + n)⦄,
      i ≠ j → i ≠ k → j ≠ k →
        orientation (deepComposePoint A B x y i)
          (deepComposePoint A B x y j) (deepComposePoint A B x y k) ≠ 0) :
    SweptConfiguration (m + n) where
  point := deepComposePoint A B x y
  sweep_strictMono := by
    intro i j hij
    by_cases hi : i.val < m
    · let ai : Fin m := ⟨i.val, hi⟩
      have hai : Fin.castAdd n ai = i := by ext; rfl
      by_cases hj : j.val < m
      · let aj : Fin m := ⟨j.val, hj⟩
        have haj : Fin.castAdd n aj = j := by ext; rfl
        rw [← hai, ← haj]
        simpa [deepComposePoint] using A.sweep_strictMono
          (show ai < aj by change i.val < j.val; exact hij)
      · have hjm : m ≤ j.val := by omega
        let bj : Fin n := ⟨j.val - m, by omega⟩
        have hbj : Fin.natAdd m bj = j := by ext; simp [bj]; omega
        rw [← hai, ← hbj]
        simpa [deepComposePoint] using hx ai bj
    · have him : m ≤ i.val := by omega
      have hjm : m ≤ j.val := by omega
      let bi : Fin n := ⟨i.val - m, by omega⟩
      let bj : Fin n := ⟨j.val - m, by omega⟩
      have hbi : Fin.natAdd m bi = i := by ext; simp [bi]; omega
      have hbj : Fin.natAdd m bj = j := by ext; simp [bj]; omega
      rw [← hbi, ← hbj]
      simpa [deepComposePoint] using B.sweep_strictMono
        (show bi < bj by change i.val - m < j.val - m; omega)
  generalPosition := hgeneral

/-- Concatenate two configurations once the two mixed orientation inequalities
have been established. General position of the union is then automatic. -/
def deepComposeSeparated {m n : ℕ} (A : SweptConfiguration m)
    (B : SweptConfiguration n) (x y : ℝ)
    (hx : ∀ i j, A.point i 0 < translatePoint x y (B.point j) 0)
    (hllr : ∀ (i j : Fin m) (k : Fin n), i < j →
      0 < orientation (A.point i) (A.point j) (translatePoint x y (B.point k)))
    (hlrr : ∀ (i : Fin m) (j k : Fin n), j < k →
      orientation (A.point i) (translatePoint x y (B.point j))
        (translatePoint x y (B.point k)) < 0) : SweptConfiguration (m + n) :=
  A.deepCompose B x y hx (deepComposePoint_generalPosition A B x y hllr hlrr)

@[simp] theorem deepCompose_point_left {m n : ℕ} (A : SweptConfiguration m)
    (B : SweptConfiguration n) (x y : ℝ) (hx hgeneral) (i : Fin m) :
    (A.deepCompose B x y hx hgeneral).point (Fin.castAdd n i) = A.point i := by
  simp [deepCompose, deepComposePoint]

@[simp] theorem deepCompose_point_right {m n : ℕ} (A : SweptConfiguration m)
    (B : SweptConfiguration n) (x y : ℝ) (hx hgeneral) (j : Fin n) :
    (A.deepCompose B x y hx hgeneral).point (Fin.natAdd m j) =
      translatePoint x y (B.point j) := by
  simp [deepCompose, deepComposePoint]

/-- A deep composition preserves the complete triple coloring of its left
component. -/
theorem deepCompose_tripleColoring_left {m n : ℕ} (A : SweptConfiguration m)
    (B : SweptConfiguration n) (x y : ℝ) (hx hgeneral) :
    (A.deepCompose B x y hx hgeneral).tripleColoring.restrict
        (Fin.castAddOrderEmb n) = A.tripleColoring := by
  funext t
  simp only [TripleColoring.restrict_apply]
  change (A.deepCompose B x y hx hgeneral).turn
      (Fin.castAdd n t.i) (Fin.castAdd n t.j) (Fin.castAdd n t.k) =
    A.turn t.i t.j t.k
  simp [SweptConfiguration.turn]

/-- A deep composition preserves the complete triple coloring of its right
component. Translation does not change orientation. -/
theorem deepCompose_tripleColoring_right {m n : ℕ} (A : SweptConfiguration m)
    (B : SweptConfiguration n) (x y : ℝ) (hx hgeneral) :
    (A.deepCompose B x y hx hgeneral).tripleColoring.restrict
        (Fin.natAddOrderEmb m) = B.tripleColoring := by
  funext t
  simp only [TripleColoring.restrict_apply]
  change (A.deepCompose B x y hx hgeneral).turn
      (Fin.natAdd m t.i) (Fin.natAdd m t.j) (Fin.natAdd m t.k) =
    B.turn t.i t.j t.k
  simp [SweptConfiguration.turn, orientation_translatePoint]

end SweptConfiguration

def HasDeepSplit {n : ℕ} (χ : TripleColoring n) (cut : ℕ) : Prop :=
  ∀ t : OrderedTriple n,
    (t.j.val < cut → cut ≤ t.k.val → χ t = Turn.left) ∧
    (t.i.val < cut → cut ≤ t.j.val → χ t = Turn.right)

/-- Number of vertices of an increasing selected sequence lying before a
split. Because the sequence is increasing, these vertices form an initial
segment. -/
def leftCount {n k : ℕ} (f : Fin k → Fin n) (cut : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin k => (f i).val < cut).card

theorem lt_leftCount_iff {n k : ℕ} {f : Fin k → Fin n}
    (hf : StrictMono f) (cut : ℕ) (i : Fin k) :
    i.val < leftCount f cut ↔ (f i).val < cut := by
  unfold leftCount
  exact Fin.lt_card_filter_univ_iff_apply_of_imp
    (fun i : Fin k => (f i).val < cut)
    (fun i j hji hi => by
      have hfji : (f j).val ≤ (f i).val := hf.monotone hji
      omega)

theorem leftCount_le {n k : ℕ} (f : Fin k → Fin n) (cut : ℕ) :
    leftCount f cut ≤ k := by
  unfold leftCount
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k))
    (fun i => (f i).val < cut)

/-- Increasing enumeration of the selected vertices before the split. -/
def leftIndexEmbedding {n k : ℕ} (f : Fin k → Fin n) (cut : ℕ) :
    Fin (leftCount f cut) ↪o Fin k :=
  Fin.castLEOrderEmb (leftCount_le f cut)

/-- Increasing enumeration of the selected vertices after the split. -/
def rightIndexEmbedding {n k : ℕ} (f : Fin k → Fin n) (cut : ℕ) :
    Fin (k - leftCount f cut) ↪o Fin k :=
  OrderEmbedding.ofStrictMono
    (fun i => (⟨leftCount f cut + i.val, by
      have := leftCount_le f cut
      omega⟩ : Fin k))
    (by
      intro i j hij
      change leftCount f cut + i.val < leftCount f cut + j.val
      omega)

@[simp] theorem leftIndexEmbedding_val {n k : ℕ} (f : Fin k → Fin n)
    (cut : ℕ) (i : Fin (leftCount f cut)) :
    (leftIndexEmbedding f cut i).val = i.val := rfl

@[simp] theorem rightIndexEmbedding_val {n k : ℕ} (f : Fin k → Fin n)
    (cut : ℕ) (i : Fin (k - leftCount f cut)) :
    (rightIndexEmbedding f cut i).val = leftCount f cut + i.val := rfl

theorem leftIndexEmbedding_before {n k : ℕ} {f : Fin k → Fin n}
    (hf : StrictMono f) (cut : ℕ) (i : Fin (leftCount f cut)) :
    (f (leftIndexEmbedding f cut i)).val < cut := by
  rw [← lt_leftCount_iff hf cut]
  simp

theorem rightIndexEmbedding_after {n k : ℕ} {f : Fin k → Fin n}
    (hf : StrictMono f) (cut : ℕ) (i : Fin (k - leftCount f cut)) :
    cut ≤ (f (rightIndexEmbedding f cut i)).val := by
  by_contra h
  have hbefore : (f (rightIndexEmbedding f cut i)).val < cut := by omega
  have hindex := (lt_leftCount_iff hf cut
    (rightIndexEmbedding f cut i)).2 hbefore
  simp at hindex

/-- Uniform upper bound on monochromatic chains of one color. -/
def ChainSizeAtMost {n : ℕ} (χ : TripleColoring n) (c : Turn)
    (bound : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃f : Fin k → Fin n⦄,
    IsMonochromaticChain χ c f → k ≤ bound

/-- The selected left part of a chain in a deep composition is a chain in
the left component. -/
theorem leftCount_le_of_component_bound {m n k bound : ℕ}
    {χ : TripleColoring (m + n)} {ψ : TripleColoring m} {c : Turn}
    (hrestrict : χ.restrict (Fin.castAddOrderEmb n) = ψ)
    {f : Fin k → Fin (m + n)} (hchain : IsMonochromaticChain χ c f)
    (hbound : ChainSizeAtMost ψ c bound) :
    leftCount f m ≤ bound := by
  rcases hchain with ⟨hf, hall⟩
  let e := leftIndexEmbedding f m
  let g : Fin (leftCount f m) → Fin m := fun i =>
    ⟨(f (e i)).val, leftIndexEmbedding_before hf m i⟩
  have hg : StrictMono g := by
    intro i j hij
    change (f (e i)).val < (f (e j)).val
    exact hf (e.strictMono hij)
  have hfactor : (Fin.castAddOrderEmb n : Fin m ↪o Fin (m + n)) ∘ g =
      f ∘ e := by
    funext i
    ext
    rfl
  have hambient : IsMonochromaticChain χ c (f ∘ e) :=
    IsMonochromaticChain.comp
      (show IsMonochromaticChain χ c f from ⟨hf, hall⟩) e
  rw [← hfactor] at hambient
  exact hbound (IsMonochromaticChain.of_comp_of_restrict_eq
    (Fin.castAddOrderEmb n) hrestrict hambient)

/-- The selected right part of a chain in a deep composition is a chain in
the right component. -/
theorem rightCount_le_of_component_bound {m n k bound : ℕ}
    {χ : TripleColoring (m + n)} {ψ : TripleColoring n} {c : Turn}
    (hrestrict : χ.restrict (Fin.natAddOrderEmb m) = ψ)
    {f : Fin k → Fin (m + n)} (hchain : IsMonochromaticChain χ c f)
    (hbound : ChainSizeAtMost ψ c bound) :
    k - leftCount f m ≤ bound := by
  rcases hchain with ⟨hf, hall⟩
  let e := rightIndexEmbedding f m
  let g : Fin (k - leftCount f m) → Fin n := fun i =>
    ⟨(f (e i)).val - m, by
      have hafter := rightIndexEmbedding_after hf m i
      have htop := (f (e i)).isLt
      omega⟩
  have hg : StrictMono g := by
    intro i j hij
    change (f (e i)).val - m < (f (e j)).val - m
    have hi := rightIndexEmbedding_after hf m i
    change m ≤ (f (e i)).val at hi
    have hmono := hf (e.strictMono hij)
    omega
  have hfactor : (Fin.natAddOrderEmb m : Fin n ↪o Fin (m + n)) ∘ g =
      f ∘ e := by
    funext i
    ext
    change m + ((f (e i)).val - m) = (f (e i)).val
    exact Nat.add_sub_of_le (rightIndexEmbedding_after hf m i)
  have hambient : IsMonochromaticChain χ c (f ∘ e) :=
    IsMonochromaticChain.comp
      (show IsMonochromaticChain χ c f from ⟨hf, hall⟩) e
  rw [← hfactor] at hambient
  exact hbound (IsMonochromaticChain.of_comp_of_restrict_eq
    (Fin.natAddOrderEmb m) hrestrict hambient)

theorem SweptConfiguration.deepCompose_hasDeepSplit {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) (x y : ℝ)
    (hx : ∀ i j, A.point i 0 < translatePoint x y (B.point j) 0)
    (hgeneral : ∀ ⦃i j k : Fin (m + n)⦄,
      i ≠ j → i ≠ k → j ≠ k →
        orientation (deepComposePoint A B x y i)
          (deepComposePoint A B x y j) (deepComposePoint A B x y k) ≠ 0)
    (hllr : ∀ (i j : Fin m) (k : Fin n), i < j →
      0 < orientation (A.point i) (A.point j) (translatePoint x y (B.point k)))
    (hlrr : ∀ (i : Fin m) (j k : Fin n), j < k →
      orientation (A.point i) (translatePoint x y (B.point j))
        (translatePoint x y (B.point k)) < 0) :
    HasDeepSplit (A.deepCompose B x y hx hgeneral).tripleColoring m := by
  intro t
  have hijv : t.i.val < t.j.val := t.hij
  have hjkv : t.j.val < t.k.val := t.hjk
  have hkbound : t.k.val < m + n := t.k.isLt
  constructor
  · intro hj hk
    have hi : t.i.val < m := by omega
    let ai : Fin m := ⟨t.i.val, hi⟩
    let aj : Fin m := ⟨t.j.val, hj⟩
    let bk : Fin n := ⟨t.k.val - m, by omega⟩
    have hai : Fin.castAdd n ai = t.i := by ext; rfl
    have haj : Fin.castAdd n aj = t.j := by ext; rfl
    have hbk : Fin.natAdd m bk = t.k := by ext; simp [bk]; omega
    change (A.deepCompose B x y hx hgeneral).turn t.i t.j t.k = Turn.left
    rw [(A.deepCompose B x y hx hgeneral).turn_eq_left_iff]
    rw [← hai, ← haj, ← hbk]
    simpa using hllr ai aj bk (by change t.i.val < t.j.val; exact t.hij)
  · intro hi hj
    have hk : m ≤ t.k.val := by omega
    let ai : Fin m := ⟨t.i.val, hi⟩
    let bj : Fin n := ⟨t.j.val - m, by omega⟩
    let bk : Fin n := ⟨t.k.val - m, by omega⟩
    have hbjbk : bj < bk := by change t.j.val - m < t.k.val - m; omega
    have hai : Fin.castAdd n ai = t.i := by ext; rfl
    have hbj : Fin.natAdd m bj = t.j := by ext; simp [bj]; omega
    have hbk : Fin.natAdd m bk = t.k := by ext; simp [bk]; omega
    change (A.deepCompose B x y hx hgeneral).turn t.i t.j t.k = Turn.right
    rw [(A.deepCompose B x y hx hgeneral).turn_eq_right_iff _ _ _ t.hij t.hjk]
    rw [← hai, ← hbj, ← hbk]
    simpa using hlrr ai bj bk hbjbk

theorem SweptConfiguration.deepComposeSeparated_hasDeepSplit {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) (x y : ℝ)
    (hx : ∀ i j, A.point i 0 < translatePoint x y (B.point j) 0)
    (hllr : ∀ (i j : Fin m) (k : Fin n), i < j →
      0 < orientation (A.point i) (A.point j) (translatePoint x y (B.point k)))
    (hlrr : ∀ (i : Fin m) (j k : Fin n), j < k →
      orientation (A.point i) (translatePoint x y (B.point j))
        (translatePoint x y (B.point k)) < 0) :
    HasDeepSplit (A.deepComposeSeparated B x y hx hllr hlrr).tripleColoring m := by
  exact A.deepCompose_hasDeepSplit B x y hx
    (deepComposePoint_generalPosition A B x y hllr hlrr) hllr hlrr

theorem SweptConfiguration.deepComposeSeparated_tripleColoring_left {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) (x y : ℝ)
    (hx : ∀ i j, A.point i 0 < translatePoint x y (B.point j) 0)
    (hllr : ∀ (i j : Fin m) (k : Fin n), i < j →
      0 < orientation (A.point i) (A.point j) (translatePoint x y (B.point k)))
    (hlrr : ∀ (i : Fin m) (j k : Fin n), j < k →
      orientation (A.point i) (translatePoint x y (B.point j))
        (translatePoint x y (B.point k)) < 0) :
    (A.deepComposeSeparated B x y hx hllr hlrr).tripleColoring.restrict
        (Fin.castAddOrderEmb n) = A.tripleColoring :=
  A.deepCompose_tripleColoring_left B x y hx
    (deepComposePoint_generalPosition A B x y hllr hlrr)

theorem SweptConfiguration.deepComposeSeparated_tripleColoring_right {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) (x y : ℝ)
    (hx : ∀ i j, A.point i 0 < translatePoint x y (B.point j) 0)
    (hllr : ∀ (i j : Fin m) (k : Fin n), i < j →
      0 < orientation (A.point i) (A.point j) (translatePoint x y (B.point k)))
    (hlrr : ∀ (i : Fin m) (j k : Fin n), j < k →
      orientation (A.point i) (translatePoint x y (B.point j))
        (translatePoint x y (B.point k)) < 0) :
    (A.deepComposeSeparated B x y hx hllr hlrr).tripleColoring.restrict
        (Fin.natAddOrderEmb m) = B.tripleColoring :=
  A.deepCompose_tripleColoring_right B x y hx
    (deepComposePoint_generalPosition A B x y hllr hlrr)

/-- Any two finite swept configurations have a genuine planar deep
composition. The right block is translated; both internal order types are
therefore retained. -/
theorem exists_deepComposition {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) :
    ∃ (P : SweptConfiguration (m + n)) (x y : ℝ),
      HasDeepSplit P.tripleColoring m ∧
      (∀ i, P.point (Fin.castAdd n i) = A.point i) ∧
      (∀ j, P.point (Fin.natAdd m j) = translatePoint x y (B.point j)) := by
  obtain ⟨x, y, hx, hllr, hlrr⟩ := exists_deepSeparationParameters A B
  let P := A.deepComposeSeparated B x y hx hllr hlrr
  refine ⟨P, x, y, A.deepComposeSeparated_hasDeepSplit B x y hx hllr hlrr, ?_, ?_⟩
  · intro i
    simp [P, SweptConfiguration.deepComposeSeparated]
  · intro j
    simp [P, SweptConfiguration.deepComposeSeparated]

/-- Coloring-level form of `exists_deepComposition`: both component order
types are retained exactly, while every mixed triple obeys the deep-split
rule. -/
theorem exists_deepComposition_coloring {m n : ℕ}
    (A : SweptConfiguration m) (B : SweptConfiguration n) :
    ∃ P : SweptConfiguration (m + n),
      HasDeepSplit P.tripleColoring m ∧
      P.tripleColoring.restrict (Fin.castAddOrderEmb n) = A.tripleColoring ∧
      P.tripleColoring.restrict (Fin.natAddOrderEmb m) = B.tripleColoring := by
  obtain ⟨x, y, hx, hllr, hlrr⟩ := exists_deepSeparationParameters A B
  let P := A.deepComposeSeparated B x y hx hllr hlrr
  exact ⟨P,
    A.deepComposeSeparated_hasDeepSplit B x y hx hllr hlrr,
    A.deepComposeSeparated_tripleColoring_left B x y hx hllr hlrr,
    A.deepComposeSeparated_tripleColoring_right B x y hx hllr hlrr⟩

namespace HasDeepSplit

variable {n cut : ℕ} {χ : TripleColoring n}

theorem left_left_right (hχ : HasDeepSplit χ cut)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hj : j.val < cut) (hk : cut ≤ k.val) :
    χ ⟨i, j, k, hij, hjk⟩ = Turn.left :=
  (hχ ⟨i, j, k, hij, hjk⟩).1 hj hk

theorem left_right_right (hχ : HasDeepSplit χ cut)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hi : i.val < cut) (hj : cut ≤ j.val) :
    χ ⟨i, j, k, hij, hjk⟩ = Turn.right :=
  (hχ ⟨i, j, k, hij, hjk⟩).2 hi hj

theorem cup_forbids_two_right (hχ : HasDeepSplit χ cut)
    {k : ℕ} {f : Fin k → Fin n}
    (hcup : IsCup χ f) {i j l : Fin k} (hij : i < j) (hjl : j < l)
    (hi : (f i).val < cut) (hj : cut ≤ (f j).val) : False := by
  rcases hcup with ⟨hf, hall⟩
  have hleft := hall hij hjl
  have hright := hχ.left_right_right (hf hij) (hf hjl) hi hj
  rw [hright] at hleft
  simp at hleft

theorem cap_forbids_two_left (hχ : HasDeepSplit χ cut)
    {k : ℕ} {f : Fin k → Fin n}
    (hcap : IsCap χ f) {i j l : Fin k} (hij : i < j) (hjl : j < l)
    (hj : (f j).val < cut) (hl : cut ≤ (f l).val) : False := by
  rcases hcap with ⟨hf, hall⟩
  have hright := hall hij hjl
  have hleft := hχ.left_left_right (hf hij) (hf hjl) hj hl
  rw [hleft] at hright
  simp at hright

/-- In a deep composition, a cup is either wholly in the right block or is
a cup from the left block followed by at most one right vertex. -/
theorem cup_chainSizeAtMost {m r a b : ℕ}
    {χ : TripleColoring (m + r)} {χleft : TripleColoring m}
    {χright : TripleColoring r}
    (hsplit : HasDeepSplit χ m)
    (hleftRestrict : χ.restrict (Fin.castAddOrderEmb r) = χleft)
    (hrightRestrict : χ.restrict (Fin.natAddOrderEmb m) = χright)
    (hleft : ChainSizeAtMost χleft Turn.left a)
    (hright : ChainSizeAtMost χright Turn.left b) :
    ChainSizeAtMost χ Turn.left (max b (a + 1)) := by
  intro k f hcup
  have hf : StrictMono f := hcup.choose
  have hL : leftCount f m ≤ a :=
    leftCount_le_of_component_bound hleftRestrict hcup hleft
  have hR : k - leftCount f m ≤ b :=
    rightCount_le_of_component_bound hrightRestrict hcup hright
  by_cases hzero : leftCount f m = 0
  · have hk : k ≤ b := by omega
    exact hk.trans (Nat.le_max_left b (a + 1))
  · have hpos : 0 < leftCount f m := Nat.pos_of_ne_zero hzero
    have hRone : k - leftCount f m ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ k - leftCount f m := by omega
      let i : Fin (leftCount f m) := ⟨0, hpos⟩
      let j : Fin (k - leftCount f m) := ⟨0, by omega⟩
      let l : Fin (k - leftCount f m) := ⟨1, by omega⟩
      apply hsplit.cup_forbids_two_right hcup
        (i := leftIndexEmbedding f m i)
        (j := rightIndexEmbedding f m j)
        (l := rightIndexEmbedding f m l)
      · change i.val < leftCount f m + j.val
        simp [i, j]
        exact hpos
      · exact (rightIndexEmbedding f m).strictMono (by simp [j, l])
      · exact leftIndexEmbedding_before hf m i
      · exact rightIndexEmbedding_after hf m j
    have hk : k ≤ a + 1 := by
      have hcount := leftCount_le f m
      omega
    exact hk.trans (Nat.le_max_right b (a + 1))

/-- Dually, a cap is either wholly in the left block or consists of at most
one left vertex followed by a cap from the right block. -/
theorem cap_chainSizeAtMost {m r a b : ℕ}
    {χ : TripleColoring (m + r)} {χleft : TripleColoring m}
    {χright : TripleColoring r}
    (hsplit : HasDeepSplit χ m)
    (hleftRestrict : χ.restrict (Fin.castAddOrderEmb r) = χleft)
    (hrightRestrict : χ.restrict (Fin.natAddOrderEmb m) = χright)
    (hleft : ChainSizeAtMost χleft Turn.right a)
    (hright : ChainSizeAtMost χright Turn.right b) :
    ChainSizeAtMost χ Turn.right (max a (b + 1)) := by
  intro k f hcap
  have hf : StrictMono f := hcap.choose
  have hL : leftCount f m ≤ a :=
    leftCount_le_of_component_bound hleftRestrict hcap hleft
  have hR : k - leftCount f m ≤ b :=
    rightCount_le_of_component_bound hrightRestrict hcap hright
  by_cases hzero : k - leftCount f m = 0
  · have hk : k ≤ a := by
      have hcount := leftCount_le f m
      omega
    exact hk.trans (Nat.le_max_left a (b + 1))
  · have hRpos : 0 < k - leftCount f m := Nat.pos_of_ne_zero hzero
    have hLone : leftCount f m ≤ 1 := by
      by_contra hnot
      have htwo : 2 ≤ leftCount f m := by omega
      let i : Fin (leftCount f m) := ⟨0, by omega⟩
      let j : Fin (leftCount f m) := ⟨1, by omega⟩
      let l : Fin (k - leftCount f m) := ⟨0, hRpos⟩
      apply hsplit.cap_forbids_two_left hcap
        (i := leftIndexEmbedding f m i)
        (j := leftIndexEmbedding f m j)
        (l := rightIndexEmbedding f m l)
      · exact (leftIndexEmbedding f m).strictMono (by simp [i, j])
      · change j.val < leftCount f m + l.val
        simp [j, l]
        omega
      · exact leftIndexEmbedding_before hf m j
      · exact rightIndexEmbedding_after hf m l
    have hk : k ≤ b + 1 := by
      have hcount := leftCount_le f m
      omega
    exact hk.trans (Nat.le_max_right a (b + 1))

/-- A deep split restricts to any increasing selected sequence. Its new cut
is exactly the number of selected vertices lying before the old cut. -/
theorem restrict (hsplit : HasDeepSplit χ cut) {k : ℕ}
    (f : Fin k ↪o Fin n) :
    HasDeepSplit (χ.restrict f) (leftCount f cut) := by
  intro t
  constructor
  · intro hj hk
    have hfj : (f t.j).val < cut :=
      (lt_leftCount_iff f.strictMono cut t.j).1 hj
    have hfk : cut ≤ (f t.k).val := by
      by_contra hnot
      have hbefore : (f t.k).val < cut := by omega
      have := (lt_leftCount_iff f.strictMono cut t.k).2 hbefore
      omega
    exact hsplit.left_left_right (f.strictMono t.hij)
      (f.strictMono t.hjk) hfj hfk
  · intro hi hj
    have hfi : (f t.i).val < cut :=
      (lt_leftCount_iff f.strictMono cut t.i).1 hi
    have hfj : cut ≤ (f t.j).val := by
      by_contra hnot
      have hbefore : (f t.j).val < cut := by omega
      have := (lt_leftCount_iff f.strictMono cut t.j).2 hbefore
      omega
    exact hsplit.left_right_right (f.strictMono t.hij)
      (f.strictMono t.hjk) hfi hfj

end HasDeepSplit

theorem IsStrongPolygon.left_triple_of_right_witness
    {n cut : ℕ} {χ : TripleColoring n} (hsplit : HasDeepSplit χ cut)
    (hstrong : IsStrongPolygon χ)
    {i j k l : Fin n} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hk : k.val < cut) (hl : cut ≤ l.val) :
    χ ⟨i, j, k, hij, hjk⟩ = Turn.left := by
  have heq := (hstrong hij hjk hkl).1
  rw [HasDeepSplit.left_left_right hsplit hij (hjk.trans hkl) (by omega) hl] at heq
  exact heq

theorem IsStrongPolygon.right_triple_of_left_witness
    {n cut : ℕ} {χ : TripleColoring n} (hsplit : HasDeepSplit χ cut)
    (hstrong : IsStrongPolygon χ)
    {i j k l : Fin n} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (hi : i.val < cut) (hj : cut ≤ j.val) :
    χ ⟨j, k, l, hjk, hkl⟩ = Turn.right := by
  have heq := (hstrong hij hjk hkl).2
  have hright := HasDeepSplit.left_right_right
    hsplit (hij.trans hjk) hkl hi (by omega)
  rw [hright] at heq
  exact heq.symm

/-- If a selected strong polygon crosses a deep split, all triples in its
left portion form a cup. -/
theorem IsStrongPolygonOn.leftPart_isCup_of_crosses
    {n k cut : ℕ} {χ : TripleColoring n} (hsplit : HasDeepSplit χ cut)
    (f : Fin k ↪o Fin n) (hstrong : IsStrongPolygonOn χ f)
    (hright : 0 < k - leftCount f cut) :
    IsCup χ (f ∘ leftIndexEmbedding f cut) := by
  let e := leftIndexEmbedding f cut
  have hsplit' : HasDeepSplit (χ.restrict f) (leftCount f cut) :=
    hsplit.restrict f
  have hcross : leftCount f cut < k := by
    have := leftCount_le f cut
    omega
  let r : Fin k := ⟨leftCount f cut, hcross⟩
  refine ⟨f.strictMono.comp e.strictMono, ?_⟩
  intro i j l hij hjl
  have hlr : e l < r := by
    change l.val < leftCount f cut
    exact l.isLt
  exact IsStrongPolygon.left_triple_of_right_witness hsplit' hstrong
    (e.strictMono hij) (e.strictMono hjl) hlr (by simp [e]) (by simp [r])

/-- Dually, the right portion of a selected strong polygon crossing a deep
split forms a cap. -/
theorem IsStrongPolygonOn.rightPart_isCap_of_crosses
    {n k cut : ℕ} {χ : TripleColoring n} (hsplit : HasDeepSplit χ cut)
    (f : Fin k ↪o Fin n) (hstrong : IsStrongPolygonOn χ f)
    (hleft : 0 < leftCount f cut) :
    IsCap χ (f ∘ rightIndexEmbedding f cut) := by
  let e := rightIndexEmbedding f cut
  have hsplit' : HasDeepSplit (χ.restrict f) (leftCount f cut) :=
    hsplit.restrict f
  let i : Fin k := ⟨leftCount f cut - 1, by
    have := leftCount_le f cut
    omega⟩
  refine ⟨f.strictMono.comp e.strictMono, ?_⟩
  intro j l r hjl hlr
  have hij : i < e j := by
    change leftCount f cut - 1 < leftCount f cut + j.val
    omega
  exact IsStrongPolygon.right_triple_of_left_witness hsplit' hstrong
    hij (e.strictMono hjl) (e.strictMono hlr) (by simp [i]; omega) (by simp [e])

/-- Quantitative crossing invariant for a deep composition. If a selected
strong polygon uses both components, its left cardinality is bounded by the
left component's cup bound and its right cardinality by the right component's
cap bound. -/
theorem IsStrongPolygonOn.card_le_of_crosses_deepSplit
    {m n k a b : ℕ} {χ : TripleColoring (m + n)}
    {χleft : TripleColoring m} {χright : TripleColoring n}
    (hsplit : HasDeepSplit χ m)
    (hleftRestrict : χ.restrict (Fin.castAddOrderEmb n) = χleft)
    (hrightRestrict : χ.restrict (Fin.natAddOrderEmb m) = χright)
    (f : Fin k ↪o Fin (m + n)) (hstrong : IsStrongPolygonOn χ f)
    (husesLeft : 0 < leftCount f m)
    (husesRight : 0 < k - leftCount f m)
    (hleftCup : ChainSizeAtMost χleft Turn.left a)
    (hrightCap : ChainSizeAtMost χright Turn.right b) :
    k ≤ a + b := by
  have hcup := hstrong.leftPart_isCup_of_crosses hsplit f husesRight
  have hcap := hstrong.rightPart_isCap_of_crosses hsplit f husesLeft
  have hL' : leftCount (f ∘ leftIndexEmbedding f m) m ≤ a :=
    leftCount_le_of_component_bound hleftRestrict hcup hleftCup
  have hleftAll : ∀ i : Fin (leftCount f m),
      ((f ∘ leftIndexEmbedding f m) i).val < m :=
    leftIndexEmbedding_before f.strictMono m
  have hleftCountEq : leftCount (f ∘ leftIndexEmbedding f m) m =
      leftCount f m := by
    have hle := leftCount_le (f ∘ leftIndexEmbedding f m) m
    by_cases hzero : leftCount f m = 0
    · omega
    · have hpos : 0 < leftCount f m := Nat.pos_of_ne_zero hzero
      let i : Fin (leftCount f m) := ⟨leftCount f m - 1, by omega⟩
      have hmono : StrictMono (f ∘ leftIndexEmbedding f m) :=
        f.strictMono.comp (leftIndexEmbedding f m).strictMono
      have hi := (lt_leftCount_iff hmono m i).2 (hleftAll i)
      change leftCount f m - 1 <
        leftCount (f ∘ leftIndexEmbedding f m) m at hi
      omega
  have hL : leftCount f m ≤ a := by simpa [hleftCountEq] using hL'
  have hR' : (k - leftCount f m) -
      leftCount (f ∘ rightIndexEmbedding f m) m ≤ b :=
    rightCount_le_of_component_bound hrightRestrict hcap hrightCap
  have hrightNone : ∀ i : Fin (k - leftCount f m),
      ¬ ((f ∘ rightIndexEmbedding f m) i).val < m := fun i hi =>
    (not_lt_of_ge (rightIndexEmbedding_after f.strictMono m i)) hi
  have hrightCountEq : leftCount (f ∘ rightIndexEmbedding f m) m = 0 := by
    by_contra hzero
    have hpos : 0 < leftCount (f ∘ rightIndexEmbedding f m) m :=
      Nat.pos_of_ne_zero hzero
    have hle := leftCount_le (f ∘ rightIndexEmbedding f m) m
    let i : Fin (k - leftCount f m) := ⟨0, by omega⟩
    have hmono : StrictMono (f ∘ rightIndexEmbedding f m) :=
      f.strictMono.comp (rightIndexEmbedding f m).strictMono
    have hi := (lt_leftCount_iff hmono m i).1 (by simp [i, hpos])
    exact hrightNone i hi
  have hR : k - leftCount f m ≤ b := by
    simpa [hrightCountEq] using hR'
  have hcount := leftCount_le f m
  omega

/-- A strong polygon cannot use two vertices from an intermediate block of
two nested, left-associated deep compositions while also using a vertex on
each side. This is the `at most one from every middle block` invariant in the
classical lower-bound construction. -/
theorem IsStrongPolygonOn.middleBlock_card_le_one
    {u v w k : ℕ} {χ : TripleColoring ((u + v) + w)}
    {χprefix : TripleColoring (u + v)}
    (houter : HasDeepSplit χ (u + v))
    (hprefix : χ.restrict (Fin.castAddOrderEmb w) = χprefix)
    (hinner : HasDeepSplit χprefix u)
    (f : Fin k ↪o Fin ((u + v) + w)) (hstrong : IsStrongPolygonOn χ f)
    (hbefore : 0 < leftCount f u)
    (hmiddle : 2 ≤ leftCount f (u + v) - leftCount f u)
    (hafter : 0 < k - leftCount f (u + v)) : False := by
  let i : Fin k := ⟨leftCount f u - 1, by
    have := leftCount_le f u
    omega⟩
  let j : Fin k := ⟨leftCount f u, by omega⟩
  let l : Fin k := ⟨leftCount f u + 1, by omega⟩
  let r : Fin k := ⟨leftCount f (u + v), by
    have := leftCount_le f (u + v)
    omega⟩
  have hij : i < j := by simp [i, j]; omega
  have hjl : j < l := by simp [j, l]
  have hlr : l < r := by simp [l, r]; omega
  have hi_u : (f i).val < u := by
    rw [← lt_leftCount_iff f.strictMono u]
    simp [i]
    omega
  have hj_u : u ≤ (f j).val := by
    by_contra hnot
    have hlt : (f j).val < u := by omega
    have := (lt_leftCount_iff f.strictMono u j).2 hlt
    simp [j] at this
  have hl_prefix : (f l).val < u + v := by
    rw [← lt_leftCount_iff f.strictMono (u + v)]
    simp [l]
    omega
  have hj_prefix : (f j).val < u + v := by
    exact lt_trans (f.strictMono hjl) hl_prefix
  have hi_prefix : (f i).val < u + v := by omega
  have hr_after : u + v ≤ (f r).val := by
    by_contra hnot
    have hlt : (f r).val < u + v := by omega
    have := (lt_leftCount_iff f.strictMono (u + v) r).2 hlt
    simp [r] at this
  let i' : Fin (u + v) := ⟨(f i).val, hi_prefix⟩
  let j' : Fin (u + v) := ⟨(f j).val, hj_prefix⟩
  let l' : Fin (u + v) := ⟨(f l).val, hl_prefix⟩
  have hi'j' : i' < j' := by change (f i).val < (f j).val; exact f.strictMono hij
  have hj'l' : j' < l' := by change (f j).val < (f l).val; exact f.strictMono hjl
  have hlocalRight :
      χprefix ⟨i', j', l', hi'j', hj'l'⟩ = Turn.right :=
    hinner.left_right_right hi'j' hj'l' hi_u hj_u
  have hprefixEq := congrFun hprefix ⟨i', j', l', hi'j', hj'l'⟩
  have hglobalRight :
      χ ⟨f i, f j, f l, f.strictMono hij, f.strictMono hjl⟩ = Turn.right := by
    exact hprefixEq.trans hlocalRight
  have hglobalLeft :
      χ ⟨f i, f j, f r, f.strictMono hij, f.strictMono (hjl.trans hlr)⟩ =
        Turn.left :=
    houter.left_left_right (f.strictMono hij)
      (f.strictMono (hjl.trans hlr)) hj_prefix hr_after
  have heq := (hstrong hij hjl hlr).1
  simp only [TripleColoring.restrict_apply] at heq
  change χ ⟨f i, f j, f l, f.strictMono hij, f.strictMono hjl⟩ =
    χ ⟨f i, f j, f r, f.strictMono hij,
      f.strictMono (hjl.trans hlr)⟩ at heq
  rw [hglobalRight, hglobalLeft] at heq
  simp at heq

end

end ErdosSzekeres
