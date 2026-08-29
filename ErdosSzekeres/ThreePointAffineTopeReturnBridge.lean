module

public import ErdosSzekeres.TopeHellyCube

@[expose] public section

namespace ErdosSzekeres
namespace TopeHellyCube

noncomputable section

/-- Coefficients `(a,b,c)` of `(x,y) ↦ a*x + b*y + c`. -/
abbrev AffineCoeff := Fin 3 → ℝ

def affineEval (c : AffineCoeff) (p : Point 2) : ℝ :=
  c 0 * p 0 + c 1 * p 1 + c 2

/-- `true` is `+1`; `false` is `-1`. -/
def boolSign : Bool → ℝ
  | true => 1
  | false => -1

def realizesBoolSign (z : ℝ) (b : Bool) : Prop :=
  match b with
  | true => 0 < z
  | false => z < 0

/-- Literal affine-functional realization; global complements are distinct. -/
def IsAffineTope {n : ℕ} (P : SweptConfiguration n)
    (τ : SignVector n) : Prop :=
  ∃ c : AffineCoeff,
    ∀ i, realizesBoolSign (affineEval c (P.point i)) (τ i)

def affineTopes {n : ℕ} (P : SweptConfiguration n) :
    Set (SignVector n) :=
  {τ | IsAffineTope P τ}

abbrev AffineTope {n : ℕ} (P : SweptConfiguration n) :=
  {τ : SignVector n // IsAffineTope P τ}

def affineTopeAdjacent {n : ℕ} (P : SweptConfiguration n)
    (σ τ : AffineTope P) : Prop :=
  cubeAdjacent σ.1 τ.1

/-- A length-`m` walk has `m+1` vertices and exactly `m` adjacent steps. -/
def AffineTopeWalk {n : ℕ} (P : SweptConfiguration n)
    (σ τ : AffineTope P) (m : ℕ) : Prop :=
  ∃ w : Fin (m + 1) → AffineTope P,
    w 0 = σ ∧
    w (Fin.last m) = τ ∧
    ∀ i : Fin m, affineTopeAdjacent P (w i.castSucc) (w i.succ)

def AffineTopeConnected {n : ℕ} (P : SweptConfiguration n) : Prop :=
  ∀ σ τ : AffineTope P, ∃ m, AffineTopeWalk P σ τ m

local instance instDecidablePredAffineTopeWalk {n : ℕ}
    (P : SweptConfiguration n) (σ τ : AffineTope P) :
    DecidablePred (AffineTopeWalk P σ τ) :=
  Classical.decPred _

/-- Minimum length of an actual walk; connectivity is an explicit producer. -/
noncomputable def affineTopeGraphDistance {n : ℕ}
    (P : SweptConfiguration n) (hP : AffineTopeConnected P)
    (σ τ : AffineTope P) : ℕ :=
  Nat.find (hP σ τ)

/-- A predecessor support has exactly `k-1` labels and satisfies the actual
project four-index law. Ambient strong-`k`-freeness is separate. -/
def StrongPredecessorEdge {n : ℕ} (χ : TripleColoring n)
    (k : ℕ) (E : Finset (Fin n)) : Prop :=
  E.card = k - 1 ∧ IsStrongPolygonSet χ E

def affineCutCE {n : ℕ} (P : SweptConfiguration n)
    (E : Finset (Fin n)) : Set (AffineTope P) :=
  {τ | nonmonochromaticOn E τ.1}

def AffineTopeIsGate {n : ℕ} (P : SweptConfiguration n)
    (hP : AffineTopeConnected P) (S : Set (AffineTope P))
    (x g : AffineTope P) : Prop :=
  g ∈ S ∧ ∀ y ∈ S,
    affineTopeGraphDistance P hP x y =
      affineTopeGraphDistance P hP x g +
        affineTopeGraphDistance P hP g y

def AffineTopeIsGated {n : ℕ} (P : SweptConfiguration n)
    (hP : AffineTopeConnected P) (S : Set (AffineTope P)) : Prop :=
  S.Nonempty ∧ ∀ x, ∃! g, AffineTopeIsGate P hP S x g

def threePointMap : Fin 3 → Point 2 :=
  ![![0, 0], ![1, 0], ![2, 1]]

def threePointConfiguration : SweptConfiguration 3 where
  point := threePointMap
  sweep_strictMono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [threePointMap]
  generalPosition := by
    intro i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [threePointMap, orientation] at *

/-- For `sᵢ = boolSign (τ i)`, these are
`a=s₁-s₀`, `b=s₂-2*s₁+s₀`, `c=s₀`. -/
def threePointCoeff (τ : SignVector 3) : AffineCoeff :=
  ![boolSign (τ 1) - boolSign (τ 0),
    boolSign (τ 2) - 2 * boolSign (τ 1) + boolSign (τ 0),
    boolSign (τ 0)]

@[simp] theorem threePointConfiguration_point_zero :
    threePointConfiguration.point 0 = ![0, 0] := by
  rfl

@[simp] theorem threePointConfiguration_point_one :
    threePointConfiguration.point 1 = ![1, 0] := by
  rfl

@[simp] theorem threePointConfiguration_point_two :
    threePointConfiguration.point 2 = ![2, 1] := by
  rfl

theorem threePointConfiguration_sweep_strictMono :
    StrictMono (fun i ↦ threePointConfiguration.point i 0) := by
  exact threePointConfiguration.sweep_strictMono

theorem threePointConfiguration_generalPosition :
    ∀ {i j k : Fin 3}, i ≠ j → i ≠ k → j ≠ k →
      orientation (threePointConfiguration.point i)
        (threePointConfiguration.point j)
        (threePointConfiguration.point k) ≠ 0 := by
  intro i j k hij hik hjk
  exact threePointConfiguration.generalPosition hij hik hjk

theorem threePointConfiguration_orientation :
    orientation (threePointConfiguration.point 0)
      (threePointConfiguration.point 1)
      (threePointConfiguration.point 2) = 1 := by
  rw [threePointConfiguration_point_zero,
    threePointConfiguration_point_one,
    threePointConfiguration_point_two]
  norm_num [orientation]

theorem threePointConfiguration_isSweepRealizable :
    IsSweepRealizable threePointConfiguration.tripleColoring := by
  exact threePointConfiguration.tripleColoring_isSweepRealizable

/-!
The next theorem is deliberately explicit about the scope ceiling: the
project's strong-polygon law needs four strictly increasing indices, so on
`Fin 3` it is vacuous for every coloring and every support. Consequently the
`n = 3`, `k = 4` predecessor edge below is literal but non-substantive; it is
not a nonvacuous project counterexample.
-/

theorem finThree_isStrongPolygonSet_vacuous
    (χ : TripleColoring 3) (s : Finset (Fin 3)) :
    IsStrongPolygonSet χ s := by
  intro i j k l hij hjk hkl
  omega

theorem threePoint_univ_card :
    (Finset.univ : Finset (Fin 3)).card = 3 := by
  simp

theorem threePoint_univ_isStrongPolygonSet :
    IsStrongPolygonSet threePointConfiguration.tripleColoring
      (Finset.univ : Finset (Fin 3)) := by
  exact finThree_isStrongPolygonSet_vacuous _ _

theorem threePoint_strongFourFree :
    ¬ ContainsStrongPolygonSet threePointConfiguration.tripleColoring
      (Finset.univ : Finset (Fin 3)) 4 := by
  rintro ⟨polygon, hsubset, hcard, _⟩
  have hle := Finset.card_le_card hsubset
  simp at hle
  omega

theorem threePoint_univ_strongPredecessorEdge :
    StrongPredecessorEdge threePointConfiguration.tripleColoring 4
      (Finset.univ : Finset (Fin 3)) := by
  exact ⟨by simp, threePoint_univ_isStrongPolygonSet⟩

theorem boolSign_realizes (b : Bool) :
    realizesBoolSign (boolSign b) b := by
  cases b <;> norm_num [boolSign, realizesBoolSign]

theorem threePointCoeff_eval (τ : SignVector 3) (i : Fin 3) :
    affineEval (threePointCoeff τ) (threePointConfiguration.point i) =
      boolSign (τ i) := by
  fin_cases i <;>
    simp [affineEval, threePointCoeff, threePointConfiguration, threePointMap] <;>
    ring

theorem threePoint_everySign_isAffineTope (τ : SignVector 3) :
    IsAffineTope threePointConfiguration τ := by
  refine ⟨threePointCoeff τ, ?_⟩
  intro i
  rw [threePointCoeff_eval]
  exact boolSign_realizes (τ i)

theorem threePoint_affineTopes_eq_univ :
    affineTopes threePointConfiguration = Set.univ := by
  ext τ
  simp only [affineTopes, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact threePoint_everySign_isAffineTope τ

def threePointTopeEquiv :
    AffineTope threePointConfiguration ≃ SignVector 3 where
  toFun τ := τ.1
  invFun τ := ⟨τ, threePoint_everySign_isAffineTope τ⟩
  left_inv τ := by exact Subtype.ext rfl
  right_inv _ := rfl

local instance instDecidableCubeAdjacentBridge {n : ℕ}
    (σ τ : SignVector n) : Decidable (cubeAdjacent σ τ) := by
  unfold cubeAdjacent
  infer_instance

private def finThreeCubeCanonicalWalk (σ τ : SignVector 3) :
    Fin (cubeGraphDistance σ τ + 1) → SignVector 3 :=
  fun i j ↦
    if (Finset.univ.filter fun k : Fin 3 =>
        k ≤ j ∧ σ k ≠ τ k).card ≤ i.val then
      τ j
    else
      σ j

private theorem finThree_cubeWalk_exact :
    ∀ σ τ : SignVector 3,
      ∃ w : Fin (cubeGraphDistance σ τ + 1) → SignVector 3,
        w 0 = σ ∧
        w (Fin.last (cubeGraphDistance σ τ)) = τ ∧
        ∀ i : Fin (cubeGraphDistance σ τ),
          cubeAdjacent (w i.castSucc) (w i.succ) := by
  intro σ τ
  have hσ : σ = ![σ 0, σ 1, σ 2] := by
    funext i
    fin_cases i <;> rfl
  have hτ : τ = ![τ 0, τ 1, τ 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hσ, hτ]
  cases hσ0 : σ 0 <;> cases hσ1 : σ 1 <;> cases hσ2 : σ 2 <;>
    cases hτ0 : τ 0 <;> cases hτ1 : τ 1 <;> cases hτ2 : τ 2 <;>
    exact ⟨finThreeCubeCanonicalWalk _ _, by decide, by decide, by decide⟩

theorem cubeGraphDistance_triangle {n : ℕ}
    (σ τ υ : SignVector n) :
    cubeGraphDistance σ υ ≤
      cubeGraphDistance σ τ + cubeGraphDistance τ υ := by
  unfold cubeGraphDistance
  have hsubset :
      (Finset.univ.filter fun i => σ i ≠ υ i) ⊆
        (Finset.univ.filter fun i => σ i ≠ τ i) ∪
          (Finset.univ.filter fun i => τ i ≠ υ i) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
    by_cases hστ : σ i = τ i
    · exact Or.inr fun hτυ ↦ hi (hστ.trans hτυ)
    · exact Or.inl hστ
  exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)

theorem cubeGraphDistance_le_of_affineTopeWalk {n : ℕ}
    {P : SweptConfiguration n} {σ τ : AffineTope P} {m : ℕ}
    (hwalk : AffineTopeWalk P σ τ m) :
    cubeGraphDistance σ.1 τ.1 ≤ m := by
  induction m generalizing σ τ with
  | zero =>
      rcases hwalk with ⟨w, hstart, hend, _⟩
      have hval : σ.1 = τ.1 := by
        calc
          σ.1 = (w 0).1 := congrArg Subtype.val hstart.symm
          _ = (w (Fin.last 0)).1 := rfl
          _ = τ.1 := congrArg Subtype.val hend
      rw [hval]
      simp [cubeGraphDistance]
  | succ m ih =>
      rcases hwalk with ⟨w, hstart, hend, hadj⟩
      let mid : AffineTope P := w (Fin.last m).castSucc
      have hprefix : AffineTopeWalk P σ mid m := by
        refine ⟨fun i ↦ w i.castSucc, ?_, ?_, ?_⟩
        · simpa using hstart
        · rfl
        · intro i
          simpa [affineTopeAdjacent] using hadj i.castSucc
      have hlast : cubeGraphDistance mid.1 τ.1 = 1 := by
        simpa [affineTopeAdjacent, mid, hend] using hadj (Fin.last m)
      have hprefixBound := ih hprefix
      have htriangle := cubeGraphDistance_triangle σ.1 mid.1 τ.1
      omega

theorem threePoint_walk_of_cubeGraphDistance
    (σ τ : AffineTope threePointConfiguration) :
    AffineTopeWalk threePointConfiguration σ τ
      (cubeGraphDistance σ.1 τ.1) := by
  obtain ⟨w, hstart, hend, hadj⟩ := finThree_cubeWalk_exact σ.1 τ.1
  refine ⟨fun i ↦ ⟨w i, threePoint_everySign_isAffineTope (w i)⟩, ?_, ?_, ?_⟩
  · exact Subtype.ext hstart
  · exact Subtype.ext hend
  · intro i
    simpa [affineTopeAdjacent] using hadj i

theorem threePoint_affineTopeConnected :
    AffineTopeConnected threePointConfiguration := by
  intro σ τ
  exact ⟨cubeGraphDistance σ.1 τ.1, threePoint_walk_of_cubeGraphDistance σ τ⟩

theorem threePoint_affineTopeGraphDistance_eq
    (σ τ : AffineTope threePointConfiguration) :
    affineTopeGraphDistance threePointConfiguration
        threePoint_affineTopeConnected σ τ =
      cubeGraphDistance σ.1 τ.1 := by
  unfold affineTopeGraphDistance
  apply Nat.le_antisymm
  · exact Nat.find_min' (threePoint_affineTopeConnected σ τ)
      (threePoint_walk_of_cubeGraphDistance σ τ)
  · exact cubeGraphDistance_le_of_affineTopeWalk
      (Nat.find_spec (threePoint_affineTopeConnected σ τ))

theorem threePoint_affineCutCE_eq :
    affineCutCE threePointConfiguration
        (Finset.univ : Finset (Fin 3)) =
      Set.preimage threePointTopeEquiv
        (↑cutCE : Set (SignVector 3)) := by
  ext τ
  simp [affineCutCE, cutCE, cut, edgeE, threePointTopeEquiv]

private theorem threePoint_mem_affineCutCE_iff
    (τ : AffineTope threePointConfiguration) :
    τ ∈ affineCutCE threePointConfiguration
        (Finset.univ : Finset (Fin 3)) ↔
      threePointTopeEquiv τ ∈ cutCE := by
  change τ ∈ affineCutCE threePointConfiguration
      (Finset.univ : Finset (Fin 3)) ↔
    τ ∈ Set.preimage threePointTopeEquiv (↑cutCE : Set (SignVector 3))
  rw [threePoint_affineCutCE_eq]

private theorem threePoint_affineTopeIsGate_iff
    (x g : AffineTope threePointConfiguration) :
    AffineTopeIsGate threePointConfiguration threePoint_affineTopeConnected
        (affineCutCE threePointConfiguration
          (Finset.univ : Finset (Fin 3))) x g ↔
      IsGate cutCE (threePointTopeEquiv x) (threePointTopeEquiv g) := by
  constructor
  · rintro ⟨hg, hall⟩
    refine ⟨(threePoint_mem_affineCutCE_iff g).mp hg, ?_⟩
    intro y hy
    let y' := threePointTopeEquiv.symm y
    have hy' : y' ∈ affineCutCE threePointConfiguration
        (Finset.univ : Finset (Fin 3)) := by
      apply (threePoint_mem_affineCutCE_iff y').mpr
      simpa [y'] using hy
    have hdist := hall y' hy'
    rw [threePoint_affineTopeGraphDistance_eq,
      threePoint_affineTopeGraphDistance_eq,
      threePoint_affineTopeGraphDistance_eq] at hdist
    simpa [y'] using hdist
  · rintro ⟨hg, hall⟩
    refine ⟨(threePoint_mem_affineCutCE_iff g).mpr hg, ?_⟩
    intro y hy
    have hdist := hall (threePointTopeEquiv y)
      ((threePoint_mem_affineCutCE_iff y).mp hy)
    rw [threePoint_affineTopeGraphDistance_eq,
      threePoint_affineTopeGraphDistance_eq,
      threePoint_affineTopeGraphDistance_eq]
    exact hdist

theorem threePoint_affineCutCE_isGated_iff :
    AffineTopeIsGated threePointConfiguration
        threePoint_affineTopeConnected
        (affineCutCE threePointConfiguration
          (Finset.univ : Finset (Fin 3))) ↔
      IsGated cutCE := by
  constructor
  · rintro ⟨hnonempty, hall⟩
    constructor
    · rcases hnonempty with ⟨g, hg⟩
      exact ⟨threePointTopeEquiv g, (threePoint_mem_affineCutCE_iff g).mp hg⟩
    · intro x
      obtain ⟨g, hg, hunique⟩ := hall (threePointTopeEquiv.symm x)
      refine ⟨threePointTopeEquiv g, ?_, ?_⟩
      · have := (threePoint_affineTopeIsGate_iff (threePointTopeEquiv.symm x) g).mp hg
        simpa using this
      · intro y hy
        let y' := threePointTopeEquiv.symm y
        have hy' : AffineTopeIsGate threePointConfiguration
            threePoint_affineTopeConnected
            (affineCutCE threePointConfiguration
              (Finset.univ : Finset (Fin 3)))
            (threePointTopeEquiv.symm x) y' := by
          apply (threePoint_affineTopeIsGate_iff _ _).mpr
          simpa [y'] using hy
        have heq : y' = g := hunique y' hy'
        simpa [y'] using congrArg threePointTopeEquiv heq
  · rintro ⟨hnonempty, hall⟩
    constructor
    · rcases hnonempty with ⟨g, hg⟩
      refine ⟨threePointTopeEquiv.symm g, ?_⟩
      apply (threePoint_mem_affineCutCE_iff _).mpr
      simpa using hg
    · intro x
      obtain ⟨g, hg, hunique⟩ := hall (threePointTopeEquiv x)
      refine ⟨threePointTopeEquiv.symm g, ?_, ?_⟩
      · apply (threePoint_affineTopeIsGate_iff _ _).mpr
        simpa using hg
      · intro y hy
        have hy' : IsGate cutCE (threePointTopeEquiv x) (threePointTopeEquiv y) :=
          (threePoint_affineTopeIsGate_iff x y).mp hy
        have heq : threePointTopeEquiv y = g := hunique _ hy'
        apply threePointTopeEquiv.injective
        simpa using heq

theorem threePointAffineTopeReturnBridge :
    IsSweepRealizable threePointConfiguration.tripleColoring ∧
    ¬ ContainsStrongPolygonSet threePointConfiguration.tripleColoring
      (Finset.univ : Finset (Fin 3)) 4 ∧
    StrongPredecessorEdge threePointConfiguration.tripleColoring 4
      (Finset.univ : Finset (Fin 3)) ∧
    affineTopes threePointConfiguration = Set.univ ∧
    AffineTopeConnected threePointConfiguration ∧
    (∀ σ τ : AffineTope threePointConfiguration,
      affineTopeGraphDistance threePointConfiguration
          threePoint_affineTopeConnected σ τ =
        cubeGraphDistance σ.1 τ.1) ∧
    affineCutCE threePointConfiguration
        (Finset.univ : Finset (Fin 3)) =
      Set.preimage threePointTopeEquiv
        (↑cutCE : Set (SignVector 3)) ∧
    (AffineTopeIsGated threePointConfiguration
        threePoint_affineTopeConnected
        (affineCutCE threePointConfiguration
          (Finset.univ : Finset (Fin 3))) ↔
      IsGated cutCE) := by
  exact ⟨threePointConfiguration_isSweepRealizable,
    threePoint_strongFourFree,
    threePoint_univ_strongPredecessorEdge,
    threePoint_affineTopes_eq_univ,
    threePoint_affineTopeConnected,
    threePoint_affineTopeGraphDistance_eq,
    threePoint_affineCutCE_eq,
    threePoint_affineCutCE_isGated_iff⟩

theorem threePoint_affineCutCE_notGated :
    ¬ AffineTopeIsGated threePointConfiguration
      threePoint_affineTopeConnected
      (affineCutCE threePointConfiguration
        (Finset.univ : Finset (Fin 3))) := by
  intro hgated
  have habstract : IsGated cutCE := threePoint_affineCutCE_isGated_iff.mp hgated
  rcases finThree_univCut_notGated with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hnotGated⟩
  exact hnotGated habstract

end

end TopeHellyCube
end ErdosSzekeres

end
