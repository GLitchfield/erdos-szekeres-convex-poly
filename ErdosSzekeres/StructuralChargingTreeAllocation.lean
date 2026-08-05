module

public import ErdosSzekeres.StructuralChargingFirstSplit
public import ErdosSzekeres.StructuralChargingPortCapacity

@[expose] public section

/-!
# Explicit decomposition trees and separating-node allocation

`IsDecomposableOn` is a proposition, so downstream charging statements should
not use its proof term as a durable node identity.  This file reifies the same
recursive data in `Type`, addresses nodes by Boolean paths, and defines the
deterministic lowest node whose two children separate a witness.
-/

namespace ErdosSzekeres

/-- A data-carrying decomposition tree for a fixed coloring and support. -/
inductive DecompositionTree {n : ℕ} (χ : TripleColoring n) :
    Finset (Fin n) → Type
  | singleton (i : Fin n) : DecompositionTree χ {i}
  | split {lower upper : Finset (Fin n)}
      (lowerTree : DecompositionTree χ lower)
      (upperTree : DecompositionTree χ upper)
      (deep : HasDeepBelowSplit χ lower upper) :
      DecompositionTree χ (lower ∪ upper)

/-- The split data found at an internal decomposition-tree node. -/
structure DecompositionSplit {n : ℕ} (χ : TripleColoring n) where
  lower : Finset (Fin n)
  upper : Finset (Fin n)
  deep : HasDeepBelowSplit χ lower upper

namespace DecompositionTree

variable {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}

/-- Forget the data-carrying tree and recover ordinary decomposability. -/
theorem toIsDecomposableOn (tree : DecompositionTree χ s) :
    IsDecomposableOn χ s := by
  induction tree with
  | singleton i => exact .singleton i
  | split lowerTree upperTree deep hlower hupper =>
      exact .split hlower hupper deep

/-- Every proposition-level decomposability proof has a data-carrying tree
witness.  The witness is not asserted to be canonical across different
decompositions. -/
theorem exists_of_isDecomposableOn (h : IsDecomposableOn χ s) :
    Nonempty (DecompositionTree χ s) := by
  induction h with
  | singleton i => exact ⟨.singleton i⟩
  | split _ _ deep hlower hupper =>
      obtain ⟨lowerTree⟩ := hlower
      obtain ⟨upperTree⟩ := hupper
      exact ⟨.split lowerTree upperTree deep⟩

/-- Look up the internal split at a Boolean path (`false` = lower child,
`true` = upper child). -/
def splitAtPath {s : Finset (Fin n)} (tree : DecompositionTree χ s) :
    List Bool → Option (DecompositionSplit χ)
  | [] =>
      match tree with
      | .singleton _ => none
      | .split _ _ deep => some ⟨_, _, deep⟩
  | direction :: path =>
      match tree with
      | .singleton _ => none
      | .split lowerTree upperTree _ =>
          if direction then upperTree.splitAtPath path
          else lowerTree.splitAtPath path

/-- The deterministic lowest separating-node address.  Descent continues
while the whole witness lies in one child and stops at the first node, viewed
from the leaves upward, whose children separate it. -/
noncomputable def lowestSeparatingPath {s witness : Finset (Fin n)}
    (tree : DecompositionTree χ s) (hwitnessSub : witness ⊆ s)
    (hwitnessCard : 2 ≤ witness.card) : List Bool := by
  classical
  induction tree generalizing witness with
  | singleton i =>
      have hcardLe : witness.card ≤ 1 := by
        calc
          witness.card ≤ ({i} : Finset (Fin n)).card :=
            Finset.card_le_card hwitnessSub
          _ = 1 := Finset.card_singleton i
      omega
  | @split lower upper lowerTree upperTree deep ihlower ihupper =>
      by_cases hlower : witness ⊆ lower
      · exact false :: ihlower hlower hwitnessCard
      by_cases hupper : witness ⊆ upper
      · exact true :: ihupper hupper hwitnessCard
      · exact []

/-- Structural characterization of a lowest separating path.  A lower step is
taken exactly when the witness lies in the lower child; an upper step records
that the lower child did not qualify; and a root stop records separation. -/
inductive IsLowestSeparatingPath {n : ℕ} {χ : TripleColoring n}
    (witness : Finset (Fin n)) :
    {s : Finset (Fin n)} → DecompositionTree χ s → List Bool → Prop
  | root {lower upper : Finset (Fin n)}
      {lowerTree : DecompositionTree χ lower}
      {upperTree : DecompositionTree χ upper}
      {deep : HasDeepBelowSplit χ lower upper}
      (hsub : witness ⊆ lower ∪ upper)
      (hnotLower : ¬witness ⊆ lower) (hnotUpper : ¬witness ⊆ upper) :
      IsLowestSeparatingPath witness (.split lowerTree upperTree deep) []
  | lower {lower upper : Finset (Fin n)}
      {lowerTree : DecompositionTree χ lower}
      {upperTree : DecompositionTree χ upper}
      {deep : HasDeepBelowSplit χ lower upper} {path : List Bool}
      (hsub : witness ⊆ lower)
      (hpath : IsLowestSeparatingPath witness lowerTree path) :
      IsLowestSeparatingPath witness (.split lowerTree upperTree deep)
        (false :: path)
  | upper {lower upper : Finset (Fin n)}
      {lowerTree : DecompositionTree χ lower}
      {upperTree : DecompositionTree χ upper}
      {deep : HasDeepBelowSplit χ lower upper} {path : List Bool}
      (hnotLower : ¬witness ⊆ lower) (hsub : witness ⊆ upper)
      (hpath : IsLowestSeparatingPath witness upperTree path) :
      IsLowestSeparatingPath witness (.split lowerTree upperTree deep)
        (true :: path)

/-- The computed address has the structural lowest-separating-path property. -/
theorem lowestSeparatingPath_isLowest {s witness : Finset (Fin n)}
    (tree : DecompositionTree χ s) (hwitnessSub : witness ⊆ s)
    (hwitnessCard : 2 ≤ witness.card) :
    IsLowestSeparatingPath witness tree
      (tree.lowestSeparatingPath hwitnessSub hwitnessCard) := by
  classical
  induction tree generalizing witness with
  | singleton i =>
      have hcardLe : witness.card ≤ 1 := by
        calc
          witness.card ≤ ({i} : Finset (Fin n)).card :=
            Finset.card_le_card hwitnessSub
          _ = 1 := Finset.card_singleton i
      omega
  | @split lower upper lowerTree upperTree deep ihlower ihupper =>
      by_cases hlower : witness ⊆ lower
      · rw [lowestSeparatingPath]
        simp only [hlower, ↓reduceDIte]
        exact .lower hlower (ihlower hlower hwitnessCard)
      by_cases hupper : witness ⊆ upper
      · rw [lowestSeparatingPath]
        simp only [hlower, hupper, ↓reduceDIte]
        exact .upper hlower hupper (ihupper hupper hwitnessCard)
      · rw [lowestSeparatingPath]
        simp only [hlower, hupper, ↓reduceDIte]
        exact .root hwitnessSub hlower hupper

/-- Every structurally lowest path equals the computed path.  Hence the
allocation is unique inside a fixed explicit decomposition tree. -/
theorem IsLowestSeparatingPath.eq_lowestSeparatingPath
    {s witness : Finset (Fin n)} {tree : DecompositionTree χ s}
    {path : List Bool} (hpath : IsLowestSeparatingPath witness tree path)
    (hwitnessSub : witness ⊆ s) (hwitnessCard : 2 ≤ witness.card) :
    path = tree.lowestSeparatingPath hwitnessSub hwitnessCard := by
  classical
  induction hpath with
  | @root lower upper lowerTree upperTree deep hsub hnotLower hnotUpper =>
      simp [lowestSeparatingPath, hnotLower, hnotUpper]
  | @lower lower upper lowerTree upperTree deep path hsub hpath ih =>
      simp only [lowestSeparatingPath, hsub, ↓reduceDIte, List.cons.injEq,
        true_and]
      exact ih hsub
  | @upper lower upper lowerTree upperTree deep path hnotLower hsub hpath ih =>
      simp only [lowestSeparatingPath, hnotLower, hsub, ↓reduceDIte,
        List.cons.injEq, true_and]
      exact ih hsub

/-- Two lowest-separating allocations in the same explicit tree have the same
node address. -/
theorem IsLowestSeparatingPath.unique
    {s witness : Finset (Fin n)} {tree : DecompositionTree χ s}
    {path path' : List Bool}
    (hpath : IsLowestSeparatingPath witness tree path)
    (hpath' : IsLowestSeparatingPath witness tree path')
    (hwitnessSub : witness ⊆ s) (hwitnessCard : 2 ≤ witness.card) :
    path = path' := by
  exact (hpath.eq_lowestSeparatingPath hwitnessSub hwitnessCard).trans
    (hpath'.eq_lowestSeparatingPath hwitnessSub hwitnessCard).symm

/-- Resolving a structurally lowest path exposes the split across which its
witness is separated. -/
theorem IsLowestSeparatingPath.splitAtPath_spec
    {s witness : Finset (Fin n)} {tree : DecompositionTree χ s}
    {path : List Bool} (hpath : IsLowestSeparatingPath witness tree path)
    {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node) :
    witness ⊆ node.lower ∪ node.upper ∧
      ¬witness ⊆ node.lower ∧ ¬witness ⊆ node.upper := by
  induction hpath generalizing node with
  | root hsub hnotLower hnotUpper =>
      simp only [splitAtPath, Option.some.injEq] at hlookup
      subst node
      exact ⟨hsub, hnotLower, hnotUpper⟩
  | lower _ _ ih =>
      exact ih hlookup
  | upper _ _ _ ih =>
      exact ih hlookup

/-- The lowest separating path resolves to an actual internal split that
contains the witness and places at least one witness vertex in each child. -/
theorem lowestSeparatingPath_spec {s witness : Finset (Fin n)}
    (tree : DecompositionTree χ s) (hwitnessSub : witness ⊆ s)
    (hwitnessCard : 2 ≤ witness.card) :
    ∃ node : DecompositionSplit χ,
      tree.splitAtPath (tree.lowestSeparatingPath hwitnessSub hwitnessCard) =
        some node ∧
      witness ⊆ node.lower ∪ node.upper ∧
      ¬witness ⊆ node.lower ∧ ¬witness ⊆ node.upper := by
  classical
  induction tree generalizing witness with
  | singleton i =>
      have hcardLe : witness.card ≤ 1 := by
        calc
          witness.card ≤ ({i} : Finset (Fin n)).card :=
            Finset.card_le_card hwitnessSub
          _ = 1 := Finset.card_singleton i
      omega
  | @split lower upper lowerTree upperTree deep ihlower ihupper =>
      by_cases hlower : witness ⊆ lower
      · obtain ⟨node, hlookup, hnodeSub, hnotLower, hnotUpper⟩ :=
          ihlower hlower hwitnessCard
        refine ⟨node, ?_, hnodeSub, hnotLower, hnotUpper⟩
        simpa [lowestSeparatingPath, hlower, splitAtPath] using hlookup
      by_cases hupper : witness ⊆ upper
      · obtain ⟨node, hlookup, hnodeSub, hnotLower, hnotUpper⟩ :=
          ihupper hupper hwitnessCard
        refine ⟨node, ?_, hnodeSub, hnotLower, hnotUpper⟩
        simp only [lowestSeparatingPath, hlower, hupper]
        convert hlookup using 1
      · refine ⟨⟨lower, upper, deep⟩, ?_, hwitnessSub, hlower, hupper⟩
        simp [lowestSeparatingPath, hlower, hupper, splitAtPath]

/-- Caps allocated to one lowest separating-node address inherit the local
two-port bound there.  This is the formal coupling between unique tree
allocation and endpoint capacity; it does not yet identify Pascal demand. -/
theorem sum_caps_at_lowest_separating_path_le
    {m : ℕ} {s : Finset (Fin n)} (tree : DecompositionTree χ s)
    (path : List Bool) (node : DecompositionSplit χ)
    (hlookup : tree.splitAtPath path = some node)
    (caps : Fin m → Finset (Fin n))
    (hsub : ∀ i, caps i ⊆ s) (hcard : ∀ i, 2 ≤ (caps i).card)
    (hcap : ∀ i, IsCapSet χ (caps i))
    (hallocated : ∀ i,
      tree.lowestSeparatingPath (hsub i) (hcard i) = path)
    (hordered : ∀ {i j}, i < j → FinsetWeaklyBefore (caps i) (caps j)) :
    (∑ i, ((caps i) ∩ node.lower).card) ≤ 2 * node.lower.card := by
  classical
  have hseparated (i : Fin m) :
      caps i ⊆ node.lower ∪ node.upper ∧
        ¬caps i ⊆ node.lower ∧ ¬caps i ⊆ node.upper := by
    obtain ⟨node', hlookup', hnodeSub, hnotLower, hnotUpper⟩ :=
      tree.lowestSeparatingPath_spec (hsub i) (hcard i)
    rw [hallocated i] at hlookup'
    have hnodeEq : node' = node := by
      exact Option.some.inj (hlookup'.symm.trans hlookup)
    subst node'
    exact ⟨hnodeSub, hnotLower, hnotUpper⟩
  have hcrossLower (i : Fin m) : ((caps i) ∩ node.lower).Nonempty := by
    have hnotUpper := (hseparated i).2.2
    rw [Finset.not_subset] at hnotUpper
    obtain ⟨q, hqCap, hqNotUpper⟩ := hnotUpper
    have hqParts := Finset.mem_union.mp ((hseparated i).1 hqCap)
    exact ⟨q, Finset.mem_inter.mpr ⟨hqCap, hqParts.resolve_right hqNotUpper⟩⟩
  have hcrossUpper (i : Fin m) : ((caps i) ∩ node.upper).Nonempty := by
    have hnotLower := (hseparated i).2.1
    rw [Finset.not_subset] at hnotLower
    obtain ⟨q, hqCap, hqNotLower⟩ := hnotLower
    have hqParts := Finset.mem_union.mp ((hseparated i).1 hqCap)
    exact ⟨q, Finset.mem_inter.mpr ⟨hqCap, hqParts.resolve_left hqNotLower⟩⟩
  exact node.deep.sum_crossing_caps_lower_card_le caps
    (fun i ↦ (hseparated i).1) hcard hcap hcrossLower hcrossUpper hordered

/-- A weakly ordered family of four-caps allocated to one tree address has at
most two members per lower-child vertex.  This is sharp, and is a cap-witness
count rather than a Pascal-overflow bound. -/
theorem allocated_ordered_four_caps_count_le_twice_lower
    {m : ℕ} {s : Finset (Fin n)} {tree : DecompositionTree χ s}
    {path : List Bool} {node : DecompositionSplit χ}
    (hlookup : tree.splitAtPath path = some node)
    (caps : Fin m → Finset (Fin n))
    (halloc : ∀ i, IsLowestSeparatingPath (caps i) tree path)
    (hcard : ∀ i, (caps i).card = 4)
    (hcap : ∀ i, IsCapSet χ (caps i))
    (hordered : ∀ {i j}, i < j → FinsetWeaklyBefore (caps i) (caps j)) :
    m ≤ 2 * node.lower.card := by
  classical
  have hseparated (i : Fin m) := (halloc i).splitAtPath_spec hlookup
  have hcrossLower (i : Fin m) : ((caps i) ∩ node.lower).Nonempty := by
    have hnotUpper := (hseparated i).2.2
    rw [Finset.not_subset] at hnotUpper
    obtain ⟨q, hqCap, hqNotUpper⟩ := hnotUpper
    have hqParts := Finset.mem_union.mp ((hseparated i).1 hqCap)
    exact ⟨q, Finset.mem_inter.mpr ⟨hqCap, hqParts.resolve_right hqNotUpper⟩⟩
  have hcrossUpper (i : Fin m) : ((caps i) ∩ node.upper).Nonempty := by
    have hnotLower := (hseparated i).2.1
    rw [Finset.not_subset] at hnotLower
    obtain ⟨q, hqCap, hqNotLower⟩ := hnotLower
    have hqParts := Finset.mem_union.mp ((hseparated i).1 hqCap)
    exact ⟨q, Finset.mem_inter.mpr ⟨hqCap, hqParts.resolve_left hqNotLower⟩⟩
  have hsum : (∑ i, ((caps i) ∩ node.lower).card) ≤
      2 * node.lower.card :=
    node.deep.sum_crossing_caps_lower_card_le caps
      (fun i ↦ (hseparated i).1) (fun i ↦ by rw [hcard i]; omega)
      hcap hcrossLower hcrossUpper hordered
  calc
    m = ∑ _i : Fin m, 1 := by simp
    _ ≤ ∑ i, ((caps i) ∩ node.lower).card := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_pos.mpr (hcrossLower i)
    _ ≤ 2 * node.lower.card := hsum

end DecompositionTree

end ErdosSzekeres

end
