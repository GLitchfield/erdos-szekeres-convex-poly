module

public import ErdosSzekeres.StrongPredecessorBicoloring

@[expose] public section

namespace ErdosSzekeres
namespace TopeHellyCube

abbrev SignVector (n : ℕ) := Fin n → Bool

/-- Hamming distance, which is the graph distance in the full sign cube. -/
def cubeGraphDistance {n : ℕ} (σ τ : SignVector n) : ℕ :=
  (Finset.univ.filter fun i => σ i ≠ τ i).card

/-- Adjacency in the full, unquotiented sign cube. -/
def cubeAdjacent {n : ℕ} (σ τ : SignVector n) : Prop :=
  cubeGraphDistance σ τ = 1

local instance instDecidableCubeAdjacent {n : ℕ} (σ τ : SignVector n) :
    Decidable (cubeAdjacent σ τ) := by
  unfold cubeAdjacent
  infer_instance

/-- Both signs occur among the coordinates selected by `E`. -/
def nonmonochromaticOn {n : ℕ} (E : Finset (Fin n))
    (τ : SignVector n) : Prop :=
  (∃ i ∈ E, τ i = true) ∧ ∃ i ∈ E, τ i = false

local instance instDecidablePredNonmonochromaticOn {n : ℕ} (E : Finset (Fin n)) :
    DecidablePred (nonmonochromaticOn E) := fun τ => by
  unfold nonmonochromaticOn
  infer_instance

/-- The finite abstract analogue of `C_E`. -/
def cut {n : ℕ} (E : Finset (Fin n)) : Finset (SignVector n) :=
  Finset.univ.filter (nonmonochromaticOn E)

/-- `g` satisfies the literal gate equation for `x` in `S`. -/
def IsGate {n : ℕ} (S : Finset (SignVector n))
    (x g : SignVector n) : Prop :=
  g ∈ S ∧ ∀ y ∈ S,
    cubeGraphDistance x y =
      cubeGraphDistance x g + cubeGraphDistance g y

local instance instDecidableIsGate {n : ℕ} (S : Finset (SignVector n))
    (x g : SignVector n) :
    Decidable (IsGate S x g) := by
  unfold IsGate
  infer_instance

/-- Every ambient vertex has a unique gate in the nonempty subset `S`. -/
def IsGated {n : ℕ} (S : Finset (SignVector n)) : Prop :=
  S.Nonempty ∧ ∀ x, ∃! g, IsGate S x g

def edgeE : Finset (Fin 3) := Finset.univ

def cutCE : Finset (SignVector 3) := cut edgeE

def x : SignVector 3 := fun _ => true

def u : SignVector 3 :=
  fun i => if i = (0 : Fin 3) then false else true

def v : SignVector 3 :=
  fun i => if i = (1 : Fin 3) then false else true

theorem finThree_univCut_notGated :
    Fintype.card (SignVector 3) = 8 ∧
    cutCE.card = 6 ∧
    x ∉ cutCE ∧
    u ∈ cutCE ∧
    v ∈ cutCE ∧
    cubeAdjacent x u ∧
    cubeAdjacent x v ∧
    cubeGraphDistance x u = 1 ∧
    cubeGraphDistance x v = 1 ∧
    cubeGraphDistance u v = 2 ∧
    (¬ ∃ g, IsGate cutCE x g) ∧
    ¬ IsGated cutCE := by
  have hCore :
      Fintype.card (SignVector 3) = 8 ∧
      cutCE.card = 6 ∧
      x ∉ cutCE ∧
      u ∈ cutCE ∧
      v ∈ cutCE ∧
      cubeAdjacent x u ∧
      cubeAdjacent x v ∧
      cubeGraphDistance x u = 1 ∧
      cubeGraphDistance x v = 1 ∧
      cubeGraphDistance u v = 2 ∧
      (¬ ∃ g, IsGate cutCE x g) := by
    decide
  rcases hCore with ⟨hCard, hCutCard, hx, hu, hv, hxu, hxv, hdxu, hdxv, hduv, hNoGate⟩
  refine ⟨hCard, hCutCard, hx, hu, hv, hxu, hxv, hdxu, hdxv, hduv, hNoGate, ?_⟩
  rintro ⟨_, hGated⟩
  obtain ⟨g, hg, _⟩ := hGated x
  exact hNoGate ⟨g, hg⟩

end TopeHellyCube
end ErdosSzekeres
