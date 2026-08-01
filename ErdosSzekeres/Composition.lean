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

end SweptConfiguration

def HasDeepSplit {n : ℕ} (χ : TripleColoring n) (cut : ℕ) : Prop :=
  ∀ t : OrderedTriple n,
    (t.j.val < cut → cut ≤ t.k.val → χ t = Turn.left) ∧
    (t.i.val < cut → cut ≤ t.j.val → χ t = Turn.right)

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

end

end ErdosSzekeres
