module

public import ErdosSzekeres.StructuralChargingResidualProbeVariable

@[expose] public section

/-!
# Choice-free witness reuse for the state-556 residual probe

This file specializes the generic residual incidence count to the unequal
five-plus-singleton carrier at state `(5,5,6)`.  It does not prove the
remaining color terminal: it exposes that terminal as a dichotomy between two
distinct strong-five witnesses and one witness serving at least ten residual
three-blocks.
-/

namespace ErdosSzekeres

/-- A bad residual three-block together with a strong-five witness supplied
by deletion of the two fixed carrier anchors and that block. -/
def IsFiveSingletonProbeWitness556 {n : ℕ} (χ : TripleColoring n)
    (ambient first singleton : Finset (Fin n)) (a b : Fin n)
    (block third : Finset (Fin n)) : Prop :=
  block ∈ BadResidualBlocks χ (ambient \ (first ∪ singleton)) 3 ∧
    third ⊆ ambient \ insert a (insert b block) ∧
    third.card = 5 ∧ IsStrongPolygonSet χ third

/-- All bad residual three-blocks served by one fixed strong-five witness. -/
noncomputable def FiveSingletonProbeFiber556 {n : ℕ}
    (χ : TripleColoring n) (ambient first singleton : Finset (Fin n))
    (a b : Fin n) (third : Finset (Fin n)) :
    Finset (Finset (Fin n)) := by
  classical
  exact (BadResidualBlocks χ (ambient \ (first ∪ singleton)) 3).filter
    (fun block ↦ IsFiveSingletonProbeWitness556 χ ambient first singleton
      a b block third)

/-- The finite, choice-free universe of strong-five witnesses incident with
at least one bad residual three-block. -/
noncomputable def FiveSingletonProbeWitnesses556 {n : ℕ}
    (χ : TripleColoring n) (ambient first singleton : Finset (Fin n))
    (a b : Fin n) : Finset (Finset (Fin n)) := by
  classical
  exact (ambient.powersetCard 5).filter fun third ↦
    ∃ block, IsFiveSingletonProbeWitness556 χ ambient first singleton
      a b block third

/-- The generic incidence count at `(R,B,C,M)=(8,3,1,9)`: either two
distinct strong-five witnesses occur, or one witness serves at least ten bad
residual three-blocks.  This is the non-tautological normalization left for
the two local color terminals at state `(5,5,6)`. -/
theorem exists_twoFiveSingletonProbeWitnesses_or_tenProbeWitness556
    {n : ℕ} {χ : TripleColoring n}
    {ambient first singleton : Finset (Fin n)}
    (hprobe : FiveSingletonResidualProbe556 χ ambient first singleton)
    (hnoStrongSix : ¬ContainsStrongPolygonSet χ ambient 6)
    {a b : Fin n} (ha : a ∈ first) (hb : b ∈ singleton) :
    (∃ third₁ ∈ FiveSingletonProbeWitnesses556 χ ambient first singleton a b,
      ∃ third₂ ∈ FiveSingletonProbeWitnesses556 χ ambient first singleton a b,
        third₁ ≠ third₂) ∨
    ∃ third ∈ FiveSingletonProbeWitnesses556 χ ambient first singleton a b,
      10 ≤ (FiveSingletonProbeFiber556 χ ambient first singleton
        a b third).card := by
  classical
  rcases hprobe with
    ⟨hfirstSub, hsingletonSub, hdisjoint, hfirstCard, hsingletonCard,
      hfirstStrong, hescape⟩
  let residual := ambient \ (first ∪ singleton)
  let witnesses :=
    FiveSingletonProbeWitnesses556 χ ambient first singleton a b
  let fiber := fun third ↦
    FiveSingletonProbeFiber556 χ ambient first singleton a b third
  let sameClass : Finset (Fin n) → Finset (Fin n) → Prop := fun _ _ ↦ True
  have hnoStrongResidual : ¬ContainsStrongPolygonSet χ residual 6 := by
    intro hstrong
    exact hnoStrongSix
      (FinsetPolygon.ContainsStrongPolygonSet.mono hstrong Finset.sdiff_subset)
  have hseedCover : ∀ seed ∈ residual.powersetCard (3 - 1),
      ∃ block ∈ BadResidualBlocks χ residual 3, seed ⊆ block := by
    intro seed hseed
    have hseedData := Finset.mem_powersetCard.mp hseed
    exact badResidualBlocks_cover_seed
      (R := 8) (W := 5) (B := 3)
      (by norm_num) (by norm_num) (by norm_num) hescape.1
      hnoStrongResidual hseedData.1 hseedData.2
  have hprobeCover : BadResidualBlocks χ residual 3 ⊆
      witnesses.biUnion fiber := by
    intro block hblock
    have hblockData :=
      Finset.mem_powersetCard.mp (Finset.mem_filter.mp hblock).1
    obtain ⟨third, hthirdSub, hthirdCard, hthirdStrong⟩ :=
      hescape.exists_witness ha hb hblockData.1 hblockData.2
    have hincident :
        IsFiveSingletonProbeWitness556 χ ambient first singleton
          a b block third := by
      exact ⟨by simpa [residual] using hblock, hthirdSub,
        hthirdCard, hthirdStrong⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨third, ?_, ?_⟩
    · change third ∈ (ambient.powersetCard 5).filter
        (fun candidate ↦ ∃ probe,
          IsFiveSingletonProbeWitness556 χ ambient first singleton
            a b probe candidate)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr
          ⟨hthirdSub.trans Finset.sdiff_subset, hthirdCard⟩,
          block, hincident⟩
    · change block ∈
        (BadResidualBlocks χ residual 3).filter
          (fun candidate ↦ IsFiveSingletonProbeWitness556 χ ambient
            first singleton a b candidate third)
      exact Finset.mem_filter.mpr ⟨hblock, hincident⟩
  have hclassBound :
      (¬∃ third₁ ∈ witnesses, ∃ third₂ ∈ witnesses,
          third₁ ≠ third₂ ∧ sameClass third₁ third₂) →
        witnesses.card ≤ 1 := by
    intro hcollision
    rw [Finset.card_le_one]
    intro third₁ hthird₁ third₂ hthird₂
    by_contra hne
    exact hcollision
      ⟨third₁, hthird₁, third₂, hthird₂, hne, trivial⟩
  have hgeneric := badResidualBlocks_collision_or_largeFiber
    (R := 8) (B := 3) (C := 1) (M := 9)
    (χ := χ) (residual := residual)
    witnesses fiber sameClass (by norm_num) hescape.1 hseedCover
    hprobeCover hclassBound (by norm_num [Nat.choose])
  rcases hgeneric with hcollision | ⟨third, hthird, hhigh⟩
  · exact Or.inl (by simpa [witnesses, sameClass] using hcollision)
  · right
    refine ⟨third, by simpa [witnesses] using hthird, ?_⟩
    have : 9 <
        (FiveSingletonProbeFiber556 χ ambient first singleton
          a b third).card := by
      simpa [fiber] using hhigh
    omega

/-- The complete ordered two-side context retained by the two state-556
color leaves.  Packaging it once prevents either leaf from silently dropping
the side cap-four exclusions or the exact fourteen-point boundary. -/
def FiveSingletonResidualProbeContext556 {n : ℕ} (χ : TripleColoring n)
    (left right first singleton : Finset (Fin n)) : Prop :=
  Disjoint left right ∧
    (∀ x ∈ left, ∀ y ∈ right, x < y) ∧
    left.card + right.card = 14 ∧
    ¬ContainsCapSet χ left 4 ∧
    ¬ContainsCapSet χ right 4 ∧
    OneChangeOn χ (left ∪ right) ∧
    ¬ContainsCapSet χ (left ∪ right) 5 ∧
    ¬ContainsCupSet χ (left ∪ right) 5 ∧
    ¬ContainsStrongPolygonSet χ (left ∪ right) 6 ∧
    FiveSingletonResidualProbe556 χ (left ∪ right) first singleton

/-- First genuine local state-556 color leaf: two distinct deletion-escape
witnesses cannot occur in the full ordered target-free context. -/
def TwoFiveSingletonProbeWitnessesImpossible556 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right first singleton : Finset (Fin n)} {a b : Fin n},
    FiveSingletonResidualProbeContext556 χ left right first singleton →
    a ∈ first → b ∈ singleton →
    (∃ third₁ ∈ FiveSingletonProbeWitnesses556 χ (left ∪ right)
        first singleton a b,
      ∃ third₂ ∈ FiveSingletonProbeWitnesses556 χ (left ∪ right)
        first singleton a b,
        third₁ ≠ third₂) → False

/-- Second genuine local state-556 color leaf: one deletion-escape witness
cannot serve ten residual three-blocks in the full ordered target-free
context. -/
def TenProbeFiveSingletonWitnessImpossible556 : Prop :=
  ∀ {n : ℕ} {χ : TripleColoring n}
      {left right first singleton : Finset (Fin n)} {a b : Fin n},
    FiveSingletonResidualProbeContext556 χ left right first singleton →
    a ∈ first → b ∈ singleton →
    (∃ third ∈ FiveSingletonProbeWitnesses556 χ (left ∪ right)
        first singleton a b,
      10 ≤ (FiveSingletonProbeFiber556 χ (left ∪ right)
        first singleton a b third).card) → False

/-- The two local witness-reuse leaves imply the older all-in-one terminal.
Neither leaf assumes `PascalTailTwoSideBound 5 5 6`; their disjunction is
supplied by the compiled incidence theorem above. -/
theorem fiveSingletonResidualProbeImpossible556_of_witnessReuseLeaves
    (htwo : TwoFiveSingletonProbeWitnessesImpossible556)
    (hten : TenProbeFiveSingletonWitnessImpossible556) :
    FiveSingletonResidualProbeImpossible556 := by
  intro n χ left right first singleton hdisjoint horder htotal
    hleftCap hrightCap hone hnoCap hnoCup hnoStrong hprobe _hbadCount
  have hcontext :
      FiveSingletonResidualProbeContext556 χ left right first singleton :=
    ⟨hdisjoint, horder, htotal, hleftCap, hrightCap, hone,
      hnoCap, hnoCup, hnoStrong, hprobe⟩
  have hprobeData := hprobe
  rcases hprobeData with
    ⟨_hfirstSub, _hsingletonSub, _hcarrierDisjoint,
      hfirstCard, hsingletonCard, _hfirstStrong, _hescape⟩
  have hfirstNonempty : first.Nonempty := Finset.card_pos.mp (by omega)
  have hsingletonNonempty : singleton.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hfirstNonempty
  obtain ⟨b, hb⟩ := hsingletonNonempty
  rcases exists_twoFiveSingletonProbeWitnesses_or_tenProbeWitness556
      hprobe hnoStrong ha hb with htwoWitnesses | htenFiber
  · exact htwo hcontext ha hb htwoWitnesses
  · exact hten hcontext ha hb htenFiber

end ErdosSzekeres

end
