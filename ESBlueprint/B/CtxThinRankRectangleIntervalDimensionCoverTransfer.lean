import ErdosSzekeres.DecomposableContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 15000

namespace ErdosSzekeres

open Ctx Ctx.Context

/-- Transfer the occupied-rank dimension cost of one cluster of thin monotone rectangles to finite list covers of the two clipped active parts of an interval cut, in either orientation. Empty active parts are handled by rank containment; nonempty cuts use the endpoint and internal finite rank-cluster budgets. Source rectangles are nonempty, all four endpoints are monotone in row position, and every chosen interval has at most two ranks. The selected source row set is convex; child active rows lie in their selected sides, their rank sets are nonempty subsets of source intervals, and new-marker reservation inequalities hold. This is an abstract finite cover-transfer statement; connecting the context recurrence to its hypotheses remains separate.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.ctx_bound_additive_sandwich_one_singleton_end -/
theorem ctx_thin_rank_rectangle_interval_dimension_cover_transfer (S K A B : Finset ℕ) (chosenInterval : Bool)
  (xl xh yl yh : ℕ → ℕ) (XA YA XB YB : ℕ → Finset ℕ)
  (hSource : ∀ p ∈ S, xl p ≤ xh p ∧ yl p ≤ yh p ∧ xh p ≤ xl p + 1)
  (hMono : ∀ p ∈ S, ∀ q ∈ S, p ≤ q →
    xl p ≤ xl q ∧ xh p ≤ xh q ∧ yl p ≤ yl q ∧ yh p ≤ yh q)
  (hKS : K ⊆ S)
  (hConvex : ∀ p ∈ K, ∀ q ∈ K, ∀ r ∈ S, p ≤ r → r ≤ q → r ∈ K)
  (hA : A ⊆ if chosenInterval then K else S \ K)
  (hB : B ⊆ if chosenInterval then S \ K else K)
  (hANonempty : ∀ p ∈ A, (XA p).Nonempty ∧ (YA p).Nonempty)
  (hBNonempty : ∀ p ∈ B, (XB p).Nonempty ∧ (YB p).Nonempty)
  (hASub : ∀ p ∈ A, XA p ⊆ Finset.Icc (xl p) (xh p) ∧ YA p ⊆ Finset.Icc (yl p) (yh p))
  (hBSub : ∀ p ∈ B, XB p ⊆ Finset.Icc (xl p) (xh p) ∧ YB p ⊆ Finset.Icc (yl p) (yh p))
  (hALeft : ∀ p ∈ A, ∀ q ∈ (if chosenInterval then S \ K else K), q < p →
    ∀ z ∈ XA p, xl q < z)
  (hARight : ∀ p ∈ A, ∀ q ∈ (if chosenInterval then S \ K else K), p < q →
    ∀ z ∈ XA p, z < xh q)
  (hBLeft : ∀ p ∈ B, ∀ q ∈ (if chosenInterval then K else S \ K), q < p →
    ∀ z ∈ YB p, yl q < z)
  (hBRight : ∀ p ∈ B, ∀ q ∈ (if chosenInterval then K else S \ K), p < q →
    ∀ z ∈ YB p, z < yh q) :
  let sourceX := fun p => Finset.Icc (xl p) (xh p)
  let sourceY := fun p => Finset.Icc (yl p) (yh p)
  let cost := fun (I : Finset ℕ) (U V : ℕ → Finset ℕ) =>
    if I = ∅ then 0 else ((I.biUnion U).card - 1) * ((I.biUnion V).card - 1) + 1
  ∃ CA CB : List (Finset ℕ),
    (∀ p ∈ A, ∃ I ∈ CA, p ∈ I) ∧ (∀ I ∈ CA, I ⊆ A) ∧
    (∀ p ∈ B, ∃ I ∈ CB, p ∈ I) ∧ (∀ I ∈ CB, I ⊆ B) ∧
    (CA.map (fun I => cost I XA YA)).sum + (CB.map (fun I => cost I XB YB)).sum ≤
      cost S sourceX sourceY := by
  classical
  have ctx_three_ordered_rank_clusters_internal_dimension_budget (X L A R : Finset ℕ) (u v c : ℕ)
    (hLX : L ⊆ X) (hAX : A ⊆ X) (hRX : R ⊆ X)
    (hL : L.Nonempty) (hA : A.Nonempty) (hR : R.Nonempty)
    (hu : 1 ≤ u) (huv : u ≤ v)
    (hBefore : u - 1 ∈ X) (hAfter : v + 1 ∈ X)
    (hLeft : ∀ z ∈ L, z ≤ u)
    (hMiddle : ∀ z ∈ A, u ≤ z ∧ z ≤ v)
    (hRight : ∀ z ∈ R, v ≤ z) (hc : 2 ≤ c) :
    L.card + A.card + R.card ≤ X.card + 2 ∧ A.card + 2 ≤ X.card ∧
      ((A.card - 1) * (c - 1) + 1) +
        ((L.card - 1) * (c - 2) + 1) + ((R.card - 1) * (c - 2) + 1) ≤
          (X.card - 1) * (c - 1) + 1 := by
    classical
    have hLA : L ∩ A ⊆ {u} := by
      intro z hz
      obtain ⟨hl, ha⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_singleton.mpr (by have := hLeft z hl; have := (hMiddle z ha).1; omega)
    have hLAR : (L ∪ A) ∩ R ⊆ {v} := by
      intro z hz
      obtain ⟨hla, hr⟩ := Finset.mem_inter.mp hz
      have hlo := hRight z hr
      have hhi : z ≤ v := by
        rcases Finset.mem_union.mp hla with hl | ha
        · exact (hLeft z hl).trans huv
        · exact (hMiddle z ha).2
      exact Finset.mem_singleton.mpr (by omega)
    have hCardLA : (L ∩ A).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hLA
    have hCardLAR : ((L ∪ A) ∩ R).card ≤ 1 := by
      simpa only [Finset.card_singleton] using Finset.card_le_card hLAR
    have hUnion : L ∪ A ∪ R ⊆ X := by
      intro z hz
      rcases Finset.mem_union.mp hz with hla | hr
      · rcases Finset.mem_union.mp hla with hl | ha
        · exact hLX hl
        · exact hAX ha
      · exact hRX hr
    have hUnionCard := Finset.card_le_card hUnion
    have hCount1 := Finset.card_union_add_card_inter L A
    have hCount2 := Finset.card_union_add_card_inter (L ∪ A) R
    have hSum : L.card + A.card + R.card ≤ X.card + 2 := by omega
    have hBeforeNot : u - 1 ∉ A := by
      intro hh
      have := (hMiddle (u - 1) hh).1
      omega
    have hAfterNot : v + 1 ∉ A := by
      intro hh
      have := (hMiddle (v + 1) hh).2
      omega
    have hDistinct : u - 1 ≠ v + 1 := by omega
    have hExtra : insert (u - 1) (insert (v + 1) A) ⊆ X := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hBefore
      · rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hAfter
        · exact hAX hz
    have hExtraCard := Finset.card_le_card hExtra
    rw [Finset.card_insert_of_notMem (by simp [hDistinct, hBeforeNot]),
      Finset.card_insert_of_notMem hAfterNot] at hExtraCard
    have hGap : A.card + 2 ≤ X.card := by omega
    have hLpos := Finset.card_pos.mpr hL
    have hApos := Finset.card_pos.mpr hA
    have hRpos := Finset.card_pos.mpr hR
    have hReduced : (A.card - 1) + (L.card - 1) + (R.card - 1) ≤ X.card - 1 := by omega
    have hMul := Nat.mul_le_mul_right (c - 2) hReduced
    have hConstant : A.card - 1 + 3 ≤ X.card - 1 + 1 := by omega
    have hStep : c - 1 = (c - 2) + 1 := by omega
    refine ⟨hSum, hGap, ?_⟩
    calc
      _ = ((A.card - 1) + (L.card - 1) + (R.card - 1)) * (c - 2) + (A.card - 1 + 3) := by
        rw [hStep]
        ring
      _ ≤ (X.card - 1) * (c - 2) + (X.card - 1 + 1) := Nat.add_le_add hMul hConstant
      _ = (X.card - 1) * (c - 1) + 1 := by
        rw [hStep]
        ring

  have ctx_two_rank_clusters_endpoint_dimension_budget (X A B : Finset ℕ) (c : ℕ)
    (hAX : A ⊆ X) (hBX : B ⊆ X) (hA : A.Nonempty) (hB : B.Nonempty)
    (hOverlap : (A ∩ B).card ≤ 1) (hMissing : ∃ z ∈ X, z ∉ A) (hc : 2 ≤ c) :
    A.card + B.card ≤ X.card + 1 ∧ A.card + 1 ≤ X.card ∧
      ((A.card - 1) * (c - 1) + 1) + ((B.card - 1) * (c - 2) + 1) ≤
        (X.card - 1) * (c - 1) + 1 := by
    classical
    have hUnion : A ∪ B ⊆ X := by
      intro z hz
      rcases Finset.mem_union.mp hz with ha | hb
      · exact hAX ha
      · exact hBX hb
    have hu := Finset.card_le_card hUnion
    have hi := Finset.card_union_add_card_inter A B
    have hSum : A.card + B.card ≤ X.card + 1 := by omega
    obtain ⟨z, hz, hzA⟩ := hMissing
    have hExtra : insert z A ⊆ X := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hz
      · exact hAX hp
    have hGap := Finset.card_le_card hExtra
    rw [Finset.card_insert_of_notMem hzA] at hGap
    have hApos := Finset.card_pos.mpr hA
    have hBpos := Finset.card_pos.mpr hB
    have hReduced : (A.card - 1) + (B.card - 1) ≤ X.card - 1 := by omega
    have hMul := Nat.mul_le_mul_right (c - 2) hReduced
    have hConstant : A.card - 1 + 2 ≤ X.card - 1 + 1 := by omega
    have hStep : c - 1 = (c - 2) + 1 := by omega
    refine ⟨hSum, hGap, ?_⟩
    calc
      _ = ((A.card - 1) + (B.card - 1)) * (c - 2) + (A.card - 1 + 2) := by
        rw [hStep]
        ring
      _ ≤ (X.card - 1) * (c - 2) + (X.card - 1 + 1) := Nat.add_le_add hMul hConstant
      _ = (X.card - 1) * (c - 1) + 1 := by
        rw [hStep]
        ring

  have ctx_three_rank_clusters_opposite_internal_dimension_budget (X L A R : Finset ℕ) (u v c : ℕ)
    (hLX : L ⊆ X) (hAX : A ⊆ X) (hRX : R ⊆ X)
    (hA : A.Nonempty) (huv : u ≤ v)
    (hLeft : ∀ z ∈ L, z ≤ u)
    (hMiddle : ∀ z ∈ A, u ≤ z ∧ z ≤ v)
    (hRight : ∀ z ∈ R, v ≤ z)
    (hShape : 2 ≤ A.card ∨ (L ∩ A = ∅ ∧ A ∩ R = ∅ ∧ L ∩ R = ∅))
    (hc : 3 ≤ c) :
    L.card + A.card + R.card ≤ X.card + 2 ∧
      (if L = ∅ then 0 else (L.card - 1) * (c - 1) + 1) +
        (if R = ∅ then 0 else (R.card - 1) * (c - 1) + 1) +
          ((A.card - 1) * (c - 3) + 1) ≤ (X.card - 1) * (c - 1) + 1 := by
    classical
    have hNonunit (hA : 2 ≤ A.card) :
      L.card + A.card + R.card ≤ X.card + 2 ∧
        (if L = ∅ then 0 else (L.card - 1) * (c - 1) + 1) +
          (if R = ∅ then 0 else (R.card - 1) * (c - 1) + 1) +
            ((A.card - 1) * (c - 3) + 1) ≤ (X.card - 1) * (c - 1) + 1 := by
      classical
      have hLA : L ∩ A ⊆ {u} := by
        intro z hz
        obtain ⟨hl, ha⟩ := Finset.mem_inter.mp hz
        exact Finset.mem_singleton.mpr (by have := hLeft z hl; have := (hMiddle z ha).1; omega)
      have hLAR : (L ∪ A) ∩ R ⊆ {v} := by
        intro z hz
        obtain ⟨hla, hr⟩ := Finset.mem_inter.mp hz
        have hlo := hRight z hr
        have hhi : z ≤ v := by
          rcases Finset.mem_union.mp hla with hl | ha
          · exact (hLeft z hl).trans huv
          · exact (hMiddle z ha).2
        exact Finset.mem_singleton.mpr (by omega)
      have hCardLA : (L ∩ A).card ≤ 1 := by
        simpa only [Finset.card_singleton] using Finset.card_le_card hLA
      have hCardLAR : ((L ∪ A) ∩ R).card ≤ 1 := by
        simpa only [Finset.card_singleton] using Finset.card_le_card hLAR
      have hUnion : L ∪ A ∪ R ⊆ X := by
        intro z hz
        rcases Finset.mem_union.mp hz with hla | hr
        · rcases Finset.mem_union.mp hla with hl | ha
          · exact hLX hl
          · exact hAX ha
        · exact hRX hr
      have hUnionCard := Finset.card_le_card hUnion
      have hCount1 := Finset.card_union_add_card_inter L A
      have hCount2 := Finset.card_union_add_card_inter (L ∪ A) R
      have hSum : L.card + A.card + R.card ≤ X.card + 2 := by omega
      have hCardRA : (R ∩ A).card ≤ 1 := by
        have hs : R ∩ A ⊆ {v} := by
          intro z hz
          have hm := Finset.mem_inter.mp hz
          have hlo := hRight z hm.1
          have hhi := (hMiddle z hm.2).2
          exact Finset.mem_singleton.mpr (by omega)
        simpa only [Finset.card_singleton] using Finset.card_le_card hs
      have hANonempty : A.Nonempty := Finset.card_pos.mp (by omega)
      have hMissingL : ∃ z ∈ X, z ∉ L := by
        by_contra hh
        push_neg at hh
        have hs : A ⊆ L := fun z hz => hh z (hAX hz)
        have he : L ∩ A = A := Finset.inter_eq_right.mpr hs
        rw [he] at hCardLA
        omega
      have hMissingR : ∃ z ∈ X, z ∉ R := by
        by_contra hh
        push_neg at hh
        have hs : A ⊆ R := fun z hz => hh z (hAX hz)
        have he : R ∩ A = A := Finset.inter_eq_right.mpr hs
        rw [he] at hCardRA
        omega
      have hMiddleMono : (A.card - 1) * (c - 3) + 1 ≤ (A.card - 1) * (c - 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega : c - 3 ≤ c - 2)) 1
      refine ⟨hSum, ?_⟩
      by_cases hL0 : L = ∅
      · rw [if_pos hL0, Nat.zero_add]
        by_cases hR0 : R = ∅
        · rw [if_pos hR0, Nat.zero_add]
          have hcA := Finset.card_le_card hAX
          exact Nat.add_le_add_right (Nat.mul_le_mul
            (by omega : A.card - 1 ≤ X.card - 1) (by omega : c - 3 ≤ c - 1)) 1
        · rw [if_neg hR0]
          have hh := ctx_two_rank_clusters_endpoint_dimension_budget X R A c hRX hAX
            (Finset.nonempty_iff_ne_empty.mpr hR0) hANonempty hCardRA hMissingR (by omega)
          exact (Nat.add_le_add_left hMiddleMono _).trans hh.2.2
      · rw [if_neg hL0]
        by_cases hR0 : R = ∅
        · rw [if_pos hR0, Nat.add_zero]
          have hh := ctx_two_rank_clusters_endpoint_dimension_budget X L A c hLX hAX
            (Finset.nonempty_iff_ne_empty.mpr hL0) hANonempty hCardLA hMissingL (by omega)
          exact (Nat.add_le_add_left hMiddleMono _).trans hh.2.2
        · rw [if_neg hR0]
          have hLpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hL0)
          have hRpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hR0)
          have hReduced : (L.card - 1) + (R.card - 1) + (A.card - 1) ≤ X.card - 1 := by omega
          have hMul := Nat.mul_le_mul_right (c - 3) hReduced
          have hConstant : 2 * ((L.card - 1) + (R.card - 1)) + 3 ≤ 2 * (X.card - 1) + 1 := by omega
          have hStep : c - 1 = (c - 3) + 2 := by omega
          calc
            _ = ((L.card - 1) + (R.card - 1) + (A.card - 1)) * (c - 3) +
                (2 * ((L.card - 1) + (R.card - 1)) + 3) := by rw [hStep]; ring
            _ ≤ (X.card - 1) * (c - 3) + (2 * (X.card - 1) + 1) := Nat.add_le_add hMul hConstant
            _ = (X.card - 1) * (c - 1) + 1 := by rw [hStep]; ring
    by_cases hTwo : 2 ≤ A.card
    · exact hNonunit hTwo
    have hOne : A.card = 1 := by have := Finset.card_pos.mpr hA; omega
    rcases hShape with hImpossible | ⟨hLA0, hAR0, hLR0⟩
    · exact False.elim (hTwo hImpossible)
    have hLA : Disjoint L A := Finset.disjoint_iff_inter_eq_empty.mpr hLA0
    have hAR : Disjoint A R := Finset.disjoint_iff_inter_eq_empty.mpr hAR0
    have hLR : Disjoint L R := Finset.disjoint_iff_inter_eq_empty.mpr hLR0
    have hLAR : Disjoint (L ∪ A) R := by
      apply Finset.disjoint_left.mpr
      intro z hz hr
      rcases Finset.mem_union.mp hz with hl | ha
      · exact Finset.disjoint_left.mp hLR hl hr
      · exact Finset.disjoint_left.mp hAR ha hr
    have hSub : L ∪ A ∪ R ⊆ X := by
      intro z hz
      rcases Finset.mem_union.mp hz with hla | hr
      · rcases Finset.mem_union.mp hla with hl | ha
        · exact hLX hl
        · exact hAX ha
      · exact hRX hr
    have hCount := Finset.card_le_card hSub
    rw [Finset.card_union_of_disjoint hLAR, Finset.card_union_of_disjoint hLA] at hCount
    have hReduced : L.card + R.card ≤ X.card - 1 := by omega
    have hCost (I : Finset ℕ) :
        (if I = ∅ then 0 else (I.card - 1) * (c - 1) + 1) ≤ I.card * (c - 1) := by
      by_cases hI : I = ∅
      · simp [hI]
      · rw [if_neg hI]
        have hIpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
        have he : I.card = I.card - 1 + 1 := by omega
        calc
          _ ≤ (I.card - 1) * (c - 1) + (c - 1) := Nat.add_le_add_left (by omega : 1 ≤ c - 1) _
          _ = I.card * (c - 1) := by
            conv_rhs => rw [he]
            ring
    refine ⟨by omega, ?_⟩
    simp only [hOne, Nat.sub_self, Nat.zero_mul, Nat.zero_add]
    have hArms := Nat.add_le_add (hCost L) (hCost R)
    have hWidth := Nat.mul_le_mul_right (c - 1) hReduced
    have hAll :
        (if L = ∅ then 0 else (L.card - 1) * (c - 1) + 1) +
          (if R = ∅ then 0 else (R.card - 1) * (c - 1) + 1) ≤ (X.card - 1) * (c - 1) := by
      calc
        _ ≤ L.card * (c - 1) + R.card * (c - 1) := hArms
        _ = (L.card + R.card) * (c - 1) := (Nat.add_mul _ _ _).symm
        _ ≤ (X.card - 1) * (c - 1) := hWidth
    exact Nat.add_le_add_right hAll 1

  classical
  let sourceX (p : ℕ) := Finset.Icc (xl p) (xh p)
  let sourceY (p : ℕ) := Finset.Icc (yl p) (yh p)
  let cost (I : Finset ℕ) (U V : ℕ → Finset ℕ) :=
    if I = ∅ then 0 else ((I.biUnion U).card - 1) * ((I.biUnion V).card - 1) + 1
  let Answer : Prop := ∃ CA CB : List (Finset ℕ),
    (∀ p ∈ A, ∃ I ∈ CA, p ∈ I) ∧ (∀ I ∈ CA, I ⊆ A) ∧
    (∀ p ∈ B, ∃ I ∈ CB, p ∈ I) ∧ (∀ I ∈ CB, I ⊆ B) ∧
    (CA.map (fun I => cost I XA YA)).sum + (CB.map (fun I => cost I XB YB)).sum ≤
      cost S sourceX sourceY
  change Answer
  have hAS : A ⊆ S := by
    cases chosenInterval
    · intro p hp
      exact (Finset.mem_sdiff.mp (hA hp)).1
    · exact hA.trans hKS
  have hBS : B ⊆ S := by
    cases chosenInterval
    · exact hB.trans hKS
    · intro p hp
      exact (Finset.mem_sdiff.mp (hB hp)).1
  have hCostMono (I J : Finset ℕ) (U V U' V' : ℕ → Finset ℕ)
      (hIJ : I ⊆ J) (hU : ∀ p ∈ I, U p ⊆ U' p) (hV : ∀ p ∈ I, V p ⊆ V' p) :
      cost I U V ≤ cost J U' V' := by
    by_cases hI : I = ∅
    · simp only [cost, hI, if_pos rfl]
      exact Nat.zero_le _
    have hJ : J ≠ ∅ := by
      intro he
      apply hI
      exact Finset.subset_empty.mp (by simpa only [he] using hIJ)
    have hu : I.biUnion U ⊆ J.biUnion U' := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_biUnion.mpr ⟨p, hIJ hp, hU p hp hz⟩
    have hv : I.biUnion V ⊆ J.biUnion V' := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      exact Finset.mem_biUnion.mpr ⟨p, hIJ hp, hV p hp hz⟩
    have huc := Finset.card_le_card hu
    have hvc := Finset.card_le_card hv
    simp only [cost, if_neg hI, if_neg hJ]
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hMonoA : cost A XA YA ≤ cost S sourceX sourceY :=
    hCostMono A S XA YA sourceX sourceY hAS (fun p hp => (hASub p hp).1) (fun p hp => (hASub p hp).2)
  have hMonoB : cost B XB YB ≤ cost S sourceX sourceY :=
    hCostMono B S XB YB sourceX sourceY hBS (fun p hp => (hBSub p hp).1) (fun p hp => (hBSub p hp).2)
  by_cases hA0 : A = ∅
  · refine ⟨[], [B], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hA0, Finset.notMem_empty, false_implies, implies_true]
    · simp only [List.not_mem_nil, false_implies, implies_true]
    · intro p hp
      exact ⟨B, by simp, hp⟩
    · intro I hI
      have he : I = B := List.mem_singleton.mp hI
      subst I
      exact fun _ h => h
    · simpa only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.zero_add, Nat.add_zero] using hMonoB
  by_cases hB0 : B = ∅
  · refine ⟨[A], [], ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      exact ⟨A, by simp, hp⟩
    · intro I hI
      have he : I = A := List.mem_singleton.mp hI
      subst I
      exact fun _ h => h
    · simp only [hB0, Finset.notMem_empty, false_implies, implies_true]
    · simp only [List.not_mem_nil, false_implies, implies_true]
    · simpa only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, Nat.zero_add, Nat.add_zero] using hMonoA
  have hAN : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA0
  have hBN : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hB0
  have hPoolSub (I J : Finset ℕ) (U V : ℕ → Finset ℕ)
      (hIJ : I ⊆ J) (hUV : ∀ p ∈ I, U p ⊆ V p) : I.biUnion U ⊆ J.biUnion V := by
    intro z hz
    obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨p, hIJ hp, hUV p hp hz⟩
  have hPoolNonempty (I : Finset ℕ) (U : ℕ → Finset ℕ)
      (hI : I.Nonempty) (hU : ∀ p ∈ I, (U p).Nonempty) : (I.biUnion U).Nonempty := by
    obtain ⟨p, hp⟩ := hI
    obtain ⟨z, hz⟩ := hU p hp
    exact ⟨z, Finset.mem_biUnion.mpr ⟨p, hp, hz⟩⟩
  have hCostCards (I : Finset ℕ) (U V : ℕ → Finset ℕ) (r c : ℕ)
      (hU : (I.biUnion U).card ≤ r) (hV : (I.biUnion V).card ≤ c) :
      cost I U V ≤ (r - 1) * (c - 1) + 1 := by
    by_cases hI : I = ∅
    · simp only [cost, hI, if_pos rfl]
      exact Nat.zero_le _
    · simp only [cost, if_neg hI]
      exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hOneOne (hBudget : cost A XA YA + cost B XB YB ≤ cost S sourceX sourceY) : Answer := by
    refine ⟨[A], [B], ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact ⟨A, by simp, hp⟩
    · intro I hI; have he := List.mem_singleton.mp hI; subst I; exact fun _ h => h
    · intro p hp; exact ⟨B, by simp, hp⟩
    · intro I hI; have he := List.mem_singleton.mp hI; subst I; exact fun _ h => h
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using hBudget
  have hOneTwo (L R : Finset ℕ) (hL : L ⊆ B) (hR : R ⊆ B) (hCover : B ⊆ L ∪ R)
      (hBudget : cost A XA YA + (cost L XB YB + cost R XB YB) ≤ cost S sourceX sourceY) : Answer := by
    refine ⟨[A], [L, R], ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact ⟨A, by simp, hp⟩
    · intro I hI; have he := List.mem_singleton.mp hI; subst I; exact fun _ h => h
    · intro p hp
      rcases Finset.mem_union.mp (hCover hp) with hl | hr
      · exact ⟨L, by simp, hl⟩
      · exact ⟨R, by simp, hr⟩
    · intro I hI
      rcases List.mem_cons.mp hI with rfl | hI
      · exact hL
      · have he := List.mem_singleton.mp hI
        subst I
        exact hR
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using hBudget
  have hTwoOne (L R : Finset ℕ) (hL : L ⊆ A) (hR : R ⊆ A) (hCover : A ⊆ L ∪ R)
      (hBudget : (cost L XA YA + cost R XA YA) + cost B XB YB ≤ cost S sourceX sourceY) : Answer := by
    refine ⟨[L, R], [B], ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_union.mp (hCover hp) with hl | hr
      · exact ⟨L, by simp, hl⟩
      · exact ⟨R, by simp, hr⟩
    · intro I hI
      rcases List.mem_cons.mp hI with rfl | hI
      · exact hL
      · have he := List.mem_singleton.mp hI
        subst I
        exact hR
    · intro p hp; exact ⟨B, by simp, hp⟩
    · intro I hI; have he := List.mem_singleton.mp hI; subst I; exact fun _ h => h
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using hBudget
  have hDisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    cases chosenInterval
    · exact (Finset.mem_sdiff.mp (hA hpA)).2 (hB hpB)
    · exact (Finset.mem_sdiff.mp (hB hpB)).2 (hA hpA)
  let X := S.biUnion sourceX
  let Y := S.biUnion sourceY
  have hXSource (p : ℕ) (hp : p ∈ S) : sourceX p ⊆ X := fun z hz =>
    Finset.mem_biUnion.mpr ⟨p, hp, hz⟩
  have hYSource (p : ℕ) (hp : p ∈ S) : sourceY p ⊆ Y := fun z hz =>
    Finset.mem_biUnion.mpr ⟨p, hp, hz⟩
  have hYTwo : 2 ≤ Y.card := by
    obtain ⟨a, ha⟩ := hAN
    obtain ⟨b, hb⟩ := hBN
    obtain ⟨z, hz⟩ := (hBNonempty b hb).2
    have hzY := hYSource b (hBS hb) ((hBSub b hb).2 hz)
    have hvalid := hSource a (hAS ha)
    have hne : a ≠ b := by
      intro he
      subst b
      exact Finset.disjoint_left.mp hDisjoint ha hb
    by_cases hab : a < b
    · have hlt := hBLeft b hb a (hA ha) hab z hz
      have hlow : yl a ∈ Y := hYSource a (hAS ha) (Finset.mem_Icc.mpr ⟨le_rfl, hvalid.2.1⟩)
      have hsub : {yl a, z} ⊆ Y := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hlow
        · have he := Finset.mem_singleton.mp hq
          subst q
          exact hzY
      have hh := Finset.card_le_card hsub
      simpa only [Finset.card_pair (by omega : yl a ≠ z)] using hh
    · have hlt := hBRight b hb a (hA ha) (by omega) z hz
      have hhigh : yh a ∈ Y := hYSource a (hAS ha) (Finset.mem_Icc.mpr ⟨hvalid.2.1, le_rfl⟩)
      have hsub : {z, yh a} ⊆ Y := by
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hzY
        · have he := Finset.mem_singleton.mp hq
          subst q
          exact hhigh
      have hh := Finset.card_le_card hsub
      simpa only [Finset.card_pair (by omega : z ≠ yh a)] using hh
  have hKN : K.Nonempty := by
    cases chosenInterval
    · obtain ⟨b, hb⟩ := hBN
      exact ⟨b, hB hb⟩
    · obtain ⟨a, ha⟩ := hAN
      exact ⟨a, hA ha⟩
  have hRestN : (S \ K).Nonempty := by
    cases chosenInterval
    · obtain ⟨a, ha⟩ := hAN
      exact ⟨a, hA ha⟩
    · obtain ⟨b, hb⟩ := hBN
      exact ⟨b, hB hb⟩
  have hSN : S.Nonempty := by obtain ⟨p, hp⟩ := hKN; exact ⟨p, hKS hp⟩
  have hSourceCost : cost S sourceX sourceY = (X.card - 1) * (Y.card - 1) + 1 := by
    simp only [cost, if_neg (Finset.nonempty_iff_ne_empty.mp hSN), X, Y]
  let firstRow := K.min' hKN
  let lastRow := K.max' hKN
  have hFirst : firstRow ∈ K := Finset.min'_mem K hKN
  have hLast : lastRow ∈ K := Finset.max'_mem K hKN
  have hFirstLe (p : ℕ) (hp : p ∈ K) : firstRow ≤ p := Finset.min'_le K p hp
  have hLeLast (p : ℕ) (hp : p ∈ K) : p ≤ lastRow := Finset.le_max' K p hp
  have hOutside (p : ℕ) (hp : p ∈ S \ K) : p < firstRow ∨ lastRow < p := by
    by_contra hh
    have hsp := Finset.mem_sdiff.mp hp
    exact hsp.2 (hConvex firstRow hFirst lastRow hLast p hsp.1 (by omega) (by omega))
  let leftRows := S.filter (· < firstRow)
  let rightRows := S.filter (lastRow < ·)
  have hLeftRows (p : ℕ) : p ∈ leftRows ↔ p ∈ S ∧ p < firstRow := by simp only [leftRows, Finset.mem_filter]
  have hRightRows (p : ℕ) : p ∈ rightRows ↔ p ∈ S ∧ lastRow < p := by simp only [rightRows, Finset.mem_filter]
  have hRestCover : S \ K ⊆ leftRows ∪ rightRows := by
    intro p hp
    have hsp := (Finset.mem_sdiff.mp hp).1
    rcases hOutside p hp with hl | hr
    · exact Finset.mem_union_left _ ((hLeftRows p).mpr ⟨hsp, hl⟩)
    · exact Finset.mem_union_right _ ((hRightRows p).mpr ⟨hsp, hr⟩)
  have hStrictCard (I J : Finset ℕ) (hIJ : I ⊆ J) (hMissing : ∃ z ∈ J, z ∉ I) :
      I.card + 1 ≤ J.card := by
    obtain ⟨z, hz, hzI⟩ := hMissing
    have hs : insert z I ⊆ J := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hz
      · exact hIJ hp
    have hh := Finset.card_le_card hs
    rwa [Finset.card_insert_of_notMem hzI] at hh
  have hEndpoint (q : ℕ) (hqS : q ∈ S)
      (hqRemoved : q ∈ if chosenInterval then S \ K else K) (rightward : Bool)
      (hAPos : ∀ p ∈ A, if rightward then q < p else p < q)
      (hBPos : ∀ p ∈ B, if rightward then p ≤ q else q ≤ p) : Answer := by
    let AX := A.biUnion XA
    let AY := A.biUnion YA
    let BX := B.biUnion XB
    let BY := B.biUnion YB
    have hAXX : AX ⊆ X := hPoolSub A S XA sourceX hAS (fun p hp => (hASub p hp).1)
    have hAYY : AY ⊆ Y := hPoolSub A S YA sourceY hAS (fun p hp => (hASub p hp).2)
    have hBXX : BX ⊆ X := hPoolSub B S XB sourceX hBS (fun p hp => (hBSub p hp).1)
    have hBYY : BY ⊆ Y := hPoolSub B S YB sourceY hBS (fun p hp => (hBSub p hp).2)
    have hAXN : AX.Nonempty := hPoolNonempty A XA hAN (fun p hp => (hANonempty p hp).1)
    have hBXN : BX.Nonempty := hPoolNonempty B XB hBN (fun p hp => (hBNonempty p hp).1)
    let boundary := if rightward then xl q + 1 else xh q - 1
    have hABound (z : ℕ) (hz : z ∈ AX) : if rightward then boundary ≤ z else z ≤ boundary := by
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hpos := hAPos p hp
      cases rightward
      · have hr := hARight p hp q hqRemoved hpos z hz
        simp only [boundary, Bool.false_eq_true, if_false, if_true]
        omega
      · have hl := hALeft p hp q hqRemoved hpos z hz
        simp only [boundary, Bool.false_eq_true, if_false, if_true]
        omega
    have hBBound (z : ℕ) (hz : z ∈ BX) : if rightward then z ≤ boundary else boundary ≤ z := by
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hpos := hBPos p hp
      have hh := Finset.mem_Icc.mp ((hBSub p hp).1 hz)
      have hthin := (hSource q hqS).2.2
      cases rightward
      · have hm := (hMono q hqS p (hBS hp) hpos).1
        simp only [boundary, Bool.false_eq_true, if_false, if_true]
        omega
      · have hm := (hMono p (hBS hp) q hqS hpos).2.1
        simp only [boundary, Bool.false_eq_true, if_false, if_true]
        omega
    have hOverlap : (AX ∩ BX).card ≤ 1 := by
      have hs : AX ∩ BX ⊆ {boundary} := by
        intro z hz
        have hm := Finset.mem_inter.mp hz
        have ha := hABound z hm.1
        have hb := hBBound z hm.2
        apply Finset.mem_singleton.mpr
        cases rightward <;> simp only [boundary, Bool.false_eq_true, if_false, if_true] at ha hb ⊢ <;> omega
      simpa only [Finset.card_singleton] using Finset.card_le_card hs
    have hMissingX : ∃ z ∈ X, z ∉ AX := by
      have hvalid := (hSource q hqS).1
      cases rightward
      · refine ⟨xh q, hXSource q hqS (Finset.mem_Icc.mpr ⟨hvalid, le_rfl⟩), ?_⟩
        intro hz
        obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        have hh := hARight p hp q hqRemoved (hAPos p hp) (xh q) hz
        omega
      · refine ⟨xl q, hXSource q hqS (Finset.mem_Icc.mpr ⟨le_rfl, hvalid⟩), ?_⟩
        intro hz
        obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        have hh := hALeft p hp q hqRemoved (hAPos p hp) (xl q) hz
        omega
    have hMissingY : ∃ z ∈ Y, z ∉ BY := by
      obtain ⟨a, ha⟩ := hAN
      have hvalid := (hSource a (hAS ha)).2.1
      cases rightward
      · refine ⟨yl a, hYSource a (hAS ha) (Finset.mem_Icc.mpr ⟨le_rfl, hvalid⟩), ?_⟩
        intro hz
        obtain ⟨b, hb, hz⟩ := Finset.mem_biUnion.mp hz
        have hposA := hAPos a ha
        have hposB := hBPos b hb
        simp only [Bool.false_eq_true, if_false, if_true] at hposA hposB
        have hh := hBLeft b hb a (hA ha) (by omega) (yl a) hz
        omega
      · refine ⟨yh a, hYSource a (hAS ha) (Finset.mem_Icc.mpr ⟨hvalid, le_rfl⟩), ?_⟩
        intro hz
        obtain ⟨b, hb, hz⟩ := Finset.mem_biUnion.mp hz
        have hposA := hAPos a ha
        have hposB := hBPos b hb
        simp only [Bool.false_eq_true, if_false, if_true] at hposA hposB
        have hh := hBRight b hb a (hA ha) (by omega) (yh a) hz
        omega
    have hBYCard : BY.card ≤ Y.card - 1 := by
      have hh := hStrictCard BY Y hBYY hMissingY
      omega
    have hCA : cost A XA YA ≤ (AX.card - 1) * (Y.card - 1) + 1 :=
      hCostCards A XA YA AX.card Y.card le_rfl (Finset.card_le_card hAYY)
    have hCB : cost B XB YB ≤ (BX.card - 1) * (Y.card - 2) + 1 := by
      simpa only [Nat.sub_sub] using hCostCards B XB YB BX.card (Y.card - 1) le_rfl hBYCard
    have hBudget := ctx_two_rank_clusters_endpoint_dimension_budget X AX BX Y.card
      hAXX hBXX hAXN hBXN hOverlap hMissingX hYTwo
    apply hOneOne
    rw [hSourceCost]
    exact (Nat.add_le_add hCA hCB).trans hBudget.2.2
  have hInternalChosen (hb : chosenInterval = true) (hLN : leftRows.Nonempty)
      (hRN : rightRows.Nonempty) : Answer := by
    subst chosenInterval
    let qL := leftRows.max' hLN
    let qR := rightRows.min' hRN
    have hqL : qL ∈ leftRows := Finset.max'_mem leftRows hLN
    have hqR : qR ∈ rightRows := Finset.min'_mem rightRows hRN
    have hqLS := (hLeftRows qL).mp hqL
    have hqRS := (hRightRows qR).mp hqR
    have hqLRest : qL ∈ S \ K := Finset.mem_sdiff.mpr ⟨hqLS.1, by
      intro hp
      have hh := hFirstLe qL hp
      omega⟩
    have hqRRest : qR ∈ S \ K := Finset.mem_sdiff.mpr ⟨hqRS.1, by
      intro hp
      have hh := hLeLast qR hp
      omega⟩
    let XL := leftRows.biUnion sourceX
    let XM := A.biUnion XA
    let XR := rightRows.biUnion sourceX
    let BL := B.filter (· < firstRow)
    let BR := B.filter (lastRow < ·)
    have hBLB : BL ⊆ B := Finset.filter_subset _ _
    have hBRB : BR ⊆ B := Finset.filter_subset _ _
    have hCover : B ⊆ BL ∪ BR := by
      intro p hp
      rcases hOutside p (hB hp) with hl | hr
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hr⟩)
    have hBLL : BL ⊆ leftRows := by
      intro p hp
      have hh := Finset.mem_filter.mp hp
      exact (hLeftRows p).mpr ⟨hBS hh.1, hh.2⟩
    have hBRR : BR ⊆ rightRows := by
      intro p hp
      have hh := Finset.mem_filter.mp hp
      exact (hRightRows p).mpr ⟨hBS hh.1, hh.2⟩
    have hLSub : leftRows ⊆ S := fun p hp => ((hLeftRows p).mp hp).1
    have hRSub : rightRows ⊆ S := fun p hp => ((hRightRows p).mp hp).1
    have hXLX : XL ⊆ X := hPoolSub leftRows S sourceX sourceX hLSub (fun _ _ => fun _ h => h)
    have hXMX : XM ⊆ X := hPoolSub A S XA sourceX hAS (fun p hp => (hASub p hp).1)
    have hXRX : XR ⊆ X := hPoolSub rightRows S sourceX sourceX hRSub (fun _ _ => fun _ h => h)
    have hXLN : XL.Nonempty := hPoolNonempty leftRows sourceX hLN (by
      intro p hp
      exact ⟨xl p, Finset.mem_Icc.mpr ⟨le_rfl, (hSource p (hLSub hp)).1⟩⟩)
    have hXMN : XM.Nonempty := hPoolNonempty A XA hAN (fun p hp => (hANonempty p hp).1)
    have hXRN : XR.Nonempty := hPoolNonempty rightRows sourceX hRN (by
      intro p hp
      exact ⟨xl p, Finset.mem_Icc.mpr ⟨le_rfl, (hSource p (hRSub hp)).1⟩⟩)
    let u := xl qL + 1
    let v := xh qR - 1
    have hu : 1 ≤ u := by dsimp only [u]; omega
    have hLeftBound : ∀ z ∈ XL, z ≤ u := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hpq : p ≤ qL := Finset.le_max' leftRows p hp
      have hmono := (hMono p (hLSub hp) qL hqLS.1 hpq).2.1
      have hthin := (hSource qL hqLS.1).2.2
      have hhi := (Finset.mem_Icc.mp hz).2
      dsimp only [u]
      omega
    have hMiddleBound : ∀ z ∈ XM, u ≤ z ∧ z ≤ v := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hpk : p ∈ K := hA hp
      have hplo := hFirstLe p hpk
      have hphi := hLeLast p hpk
      have hleft := hALeft p hp qL hqLRest (by omega) z hz
      have hright := hARight p hp qR hqRRest (by omega) z hz
      dsimp only [u, v]
      omega
    have hRightBound : ∀ z ∈ XR, v ≤ z := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hqp : qR ≤ p := Finset.min'_le rightRows p hp
      have hmono := (hMono qR hqRS.1 p (hRSub hp) hqp).1
      have hthin := (hSource qR hqRS.1).2.2
      have hlo := (Finset.mem_Icc.mp hz).1
      dsimp only [v]
      omega
    have huv : u ≤ v := by obtain ⟨z, hz⟩ := hXMN; have hh := hMiddleBound z hz; omega
    have hBefore : u - 1 ∈ X := by
      have hh := hXSource qL hqLS.1 (Finset.mem_Icc.mpr ⟨le_rfl, (hSource qL hqLS.1).1⟩)
      simpa only [u, Nat.add_sub_cancel] using hh
    have hAfter : v + 1 ∈ X := by
      have hh := hXSource qR hqRS.1 (Finset.mem_Icc.mpr ⟨(hSource qR hqRS.1).1, le_rfl⟩)
      have hhigh : 1 ≤ xh qR := by
        obtain ⟨z, hz⟩ := hXMN
        have hm := hMiddleBound z hz
        dsimp only [u, v] at hm
        omega
      have he : v + 1 = xh qR := by dsimp only [v]; omega
      simpa only [he] using hh
    have hAY : A.biUnion YA ⊆ Y := hPoolSub A S YA sourceY hAS (fun p hp => (hASub p hp).2)
    have hBLX : BL.biUnion XB ⊆ XL :=
      hPoolSub BL leftRows XB sourceX hBLL (fun p hp => (hBSub p (hBLB hp)).1)
    have hBRX : BR.biUnion XB ⊆ XR :=
      hPoolSub BR rightRows XB sourceX hBRR (fun p hp => (hBSub p (hBRB hp)).1)
    have hBLY : BL.biUnion YB ⊆ Y :=
      hPoolSub BL S YB sourceY (hBLB.trans hBS) (fun p hp => (hBSub p (hBLB hp)).2)
    have hBRY : BR.biUnion YB ⊆ Y :=
      hPoolSub BR S YB sourceY (hBRB.trans hBS) (fun p hp => (hBSub p (hBRB hp)).2)
    have hLeftMissing : ∃ z ∈ Y, z ∉ BL.biUnion YB := by
      refine ⟨yh firstRow, hYSource firstRow (hKS hFirst)
        (Finset.mem_Icc.mpr ⟨(hSource firstRow (hKS hFirst)).2.1, le_rfl⟩), ?_⟩
      intro hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hm := Finset.mem_filter.mp hp
      have hh := hBRight p hm.1 firstRow hFirst hm.2 (yh firstRow) hz
      omega
    have hRightMissing : ∃ z ∈ Y, z ∉ BR.biUnion YB := by
      refine ⟨yl lastRow, hYSource lastRow (hKS hLast)
        (Finset.mem_Icc.mpr ⟨le_rfl, (hSource lastRow (hKS hLast)).2.1⟩), ?_⟩
      intro hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hm := Finset.mem_filter.mp hp
      have hh := hBLeft p hm.1 lastRow hLast hm.2 (yl lastRow) hz
      omega
    have hLeftCard : (BL.biUnion YB).card ≤ Y.card - 1 := by
      have hh := hStrictCard _ _ hBLY hLeftMissing
      omega
    have hRightCard : (BR.biUnion YB).card ≤ Y.card - 1 := by
      have hh := hStrictCard _ _ hBRY hRightMissing
      omega
    have hCA : cost A XA YA ≤ (XM.card - 1) * (Y.card - 1) + 1 :=
      hCostCards A XA YA XM.card Y.card le_rfl (Finset.card_le_card hAY)
    have hCL : cost BL XB YB ≤ (XL.card - 1) * (Y.card - 2) + 1 := by
      simpa only [Nat.sub_sub] using hCostCards BL XB YB XL.card (Y.card - 1)
        (Finset.card_le_card hBLX) hLeftCard
    have hCR : cost BR XB YB ≤ (XR.card - 1) * (Y.card - 2) + 1 := by
      simpa only [Nat.sub_sub] using hCostCards BR XB YB XR.card (Y.card - 1)
        (Finset.card_le_card hBRX) hRightCard
    have hBudget := ctx_three_ordered_rank_clusters_internal_dimension_budget X XL XM XR u v Y.card
      hXLX hXMX hXRX hXLN hXMN hXRN hu huv hBefore hAfter hLeftBound hMiddleBound hRightBound hYTwo
    apply hOneTwo BL BR hBLB hBRB hCover
    rw [hSourceCost]
    have hh := Nat.add_le_add hCA (Nat.add_le_add hCL hCR)
    have hb := hBudget.2.2
    omega
  have hInternalOpposite (hb : chosenInterval = false) (hLN : leftRows.Nonempty)
      (hRN : rightRows.Nonempty) : Answer := by
    subst chosenInterval
    obtain ⟨qL, hqL⟩ := hLN
    obtain ⟨qR, hqR⟩ := hRN
    have hqLS := (hLeftRows qL).mp hqL
    have hqRS := (hRightRows qR).mp hqR
    have hqLRest : qL ∈ S \ K := Finset.mem_sdiff.mpr ⟨hqLS.1, by
      intro hp
      have hh := hFirstLe qL hp
      omega⟩
    have hqRRest : qR ∈ S \ K := Finset.mem_sdiff.mpr ⟨hqRS.1, by
      intro hp
      have hh := hLeLast qR hp
      omega⟩
    let AL := A.filter (· < firstRow)
    let AR := A.filter (lastRow < ·)
    let XL := AL.biUnion XA
    let XM := K.biUnion sourceX
    let XR := AR.biUnion XA
    let BY := B.biUnion YB
    have hALA : AL ⊆ A := Finset.filter_subset _ _
    have hARA : AR ⊆ A := Finset.filter_subset _ _
    have hCover : A ⊆ AL ∪ AR := by
      intro p hp
      rcases hOutside p (hA hp) with hl | hr
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hr⟩)
    have hXLX : XL ⊆ X := hPoolSub AL S XA sourceX (hALA.trans hAS) (fun p hp => (hASub p (hALA hp)).1)
    have hXMX : XM ⊆ X := hPoolSub K S sourceX sourceX hKS (fun _ _ => fun _ h => h)
    have hXRX : XR ⊆ X := hPoolSub AR S XA sourceX (hARA.trans hAS) (fun p hp => (hASub p (hARA hp)).1)
    have hXMN : XM.Nonempty := hPoolNonempty K sourceX hKN (by
      intro p hp
      exact ⟨xl p, Finset.mem_Icc.mpr ⟨le_rfl, (hSource p (hKS hp)).1⟩⟩)
    let u := xl firstRow
    let v := xh lastRow
    have huXM : u ∈ XM := Finset.mem_biUnion.mpr ⟨firstRow, hFirst,
      Finset.mem_Icc.mpr ⟨le_rfl, (hSource firstRow (hKS hFirst)).1⟩⟩
    have hvXM : v ∈ XM := Finset.mem_biUnion.mpr ⟨lastRow, hLast,
      Finset.mem_Icc.mpr ⟨(hSource lastRow (hKS hLast)).1, le_rfl⟩⟩
    have hLeftBound : ∀ z ∈ XL, z ≤ u := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hm := Finset.mem_filter.mp hp
      have hr := hARight p hm.1 firstRow hFirst hm.2 z hz
      have hthin := (hSource firstRow (hKS hFirst)).2.2
      dsimp only [u]
      omega
    have hMiddleBound : ∀ z ∈ XM, u ≤ z ∧ z ≤ v := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hlo := (hMono firstRow (hKS hFirst) p (hKS hp) (hFirstLe p hp)).1
      have hhi := (hMono p (hKS hp) lastRow (hKS hLast) (hLeLast p hp)).2.1
      have hm := Finset.mem_Icc.mp hz
      dsimp only [u, v]
      omega
    have hRightBound : ∀ z ∈ XR, v ≤ z := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hm := Finset.mem_filter.mp hp
      have hl := hALeft p hm.1 lastRow hLast hm.2 z hz
      have hthin := (hSource lastRow (hKS hLast)).2.2
      dsimp only [v]
      omega
    have huv : u ≤ v := (hMiddleBound u huXM).2
    have hShape : 2 ≤ XM.card ∨ (XL ∩ XM = ∅ ∧ XM ∩ XR = ∅ ∧ XL ∩ XR = ∅) := by
      by_cases hTwo : 2 ≤ XM.card
      · exact Or.inl hTwo
      right
      have hUnique : ∀ a ∈ XM, ∀ b ∈ XM, a = b := Finset.card_le_one.mp (by omega)
      have hFirstHigh : xh firstRow = u := hUnique _
        (Finset.mem_biUnion.mpr ⟨firstRow, hFirst,
          Finset.mem_Icc.mpr ⟨(hSource firstRow (hKS hFirst)).1, le_rfl⟩⟩) u huXM
      have hLastLow : xl lastRow = u := hUnique _
        (Finset.mem_biUnion.mpr ⟨lastRow, hLast,
          Finset.mem_Icc.mpr ⟨le_rfl, (hSource lastRow (hKS hLast)).1⟩⟩) u huXM
      have hLStrict : ∀ z ∈ XL, z < u := by
        intro z hz
        obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        have hm := Finset.mem_filter.mp hp
        have hh := hARight p hm.1 firstRow hFirst hm.2 z hz
        simpa only [hFirstHigh] using hh
      have hRStrict : ∀ z ∈ XR, u < z := by
        intro z hz
        obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
        have hm := Finset.mem_filter.mp hp
        have hh := hALeft p hm.1 lastRow hLast hm.2 z hz
        simpa only [hLastLow] using hh
      refine ⟨?_, ?_, ?_⟩
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hm := Finset.mem_inter.mp hz
        have he := hUnique z hm.2 u huXM
        have hh := hLStrict z hm.1
        omega
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hm := Finset.mem_inter.mp hz
        have he := hUnique z hm.1 u huXM
        have hh := hRStrict z hm.2
        omega
      · apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hm := Finset.mem_inter.mp hz
        have hl := hLStrict z hm.1
        have hr := hRStrict z hm.2
        omega
    have hBYY : BY ⊆ Y := hPoolSub B S YB sourceY hBS (fun p hp => (hBSub p hp).2)
    have hBYN : BY.Nonempty := hPoolNonempty B YB hBN (fun p hp => (hBNonempty p hp).2)
    have hBYBounds : ∀ z ∈ BY, yl qL < z ∧ z < yh qR := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := Finset.mem_biUnion.mp hz
      have hlo := hFirstLe p (hB hp)
      have hhi := hLeLast p (hB hp)
      exact ⟨hBLeft p hp qL hqLRest (by omega) z hz,
        hBRight p hp qR hqRRest (by omega) z hz⟩
    have hLowY : yl qL ∈ Y := hYSource qL hqLS.1
      (Finset.mem_Icc.mpr ⟨le_rfl, (hSource qL hqLS.1).2.1⟩)
    have hHighY : yh qR ∈ Y := hYSource qR hqRS.1
      (Finset.mem_Icc.mpr ⟨(hSource qR hqRS.1).2.1, le_rfl⟩)
    have hLowNot : yl qL ∉ BY := by intro hz; have hh := (hBYBounds _ hz).1; omega
    have hHighNot : yh qR ∉ BY := by intro hz; have hh := (hBYBounds _ hz).2; omega
    have hDistinct : yh qR ≠ yl qL := by
      obtain ⟨z, hz⟩ := hBYN
      have hh := hBYBounds z hz
      omega
    have hInserted : insert (yl qL) BY ⊆ Y := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hLowY
      · exact hBYY hz
    have hGap : BY.card + 2 ≤ Y.card := by
      have hh := hStrictCard (insert (yl qL) BY) Y hInserted
        ⟨yh qR, hHighY, by simp [hDistinct, hHighNot]⟩
      rw [Finset.card_insert_of_notMem hLowNot] at hh
      omega
    have hYThree : 3 ≤ Y.card := by have := Finset.card_pos.mpr hBYN; omega
    have hBXSub : B.biUnion XB ⊆ XM := hPoolSub B K XB sourceX hB (fun p hp => (hBSub p hp).1)
    have hCB : cost B XB YB ≤ (XM.card - 1) * (Y.card - 3) + 1 := by
      simpa only [Nat.sub_sub] using hCostCards B XB YB XM.card (Y.card - 2)
        (Finset.card_le_card hBXSub) (by omega : BY.card ≤ Y.card - 2)
    have hArmCost (I : Finset ℕ) (hIA : I ⊆ A) :
        cost I XA YA ≤ if I.biUnion XA = ∅ then 0 else ((I.biUnion XA).card - 1) * (Y.card - 1) + 1 := by
      by_cases hIX : I.biUnion XA = ∅
      · have hI0 : I = ∅ := by
          by_contra hn
          have hnon := hPoolNonempty I XA (Finset.nonempty_iff_ne_empty.mpr hn)
            (fun p hp => (hANonempty p (hIA hp)).1)
          exact Finset.nonempty_iff_ne_empty.mp hnon hIX
        simp only [cost, hI0, Finset.biUnion_empty, if_pos rfl, if_true, le_refl]
      · rw [if_neg hIX]
        have hy := hPoolSub I S YA sourceY (hIA.trans hAS) (fun p hp => (hASub p (hIA hp)).2)
        exact hCostCards I XA YA (I.biUnion XA).card Y.card le_rfl (Finset.card_le_card hy)
    have hCL : cost AL XA YA ≤ if XL = ∅ then 0 else (XL.card - 1) * (Y.card - 1) + 1 := hArmCost AL hALA
    have hCR : cost AR XA YA ≤ if XR = ∅ then 0 else (XR.card - 1) * (Y.card - 1) + 1 := hArmCost AR hARA
    have hBudget := ctx_three_rank_clusters_opposite_internal_dimension_budget X XL XM XR u v Y.card
      hXLX hXMX hXRX hXMN huv hLeftBound hMiddleBound hRightBound hShape hYThree
    apply hTwoOne AL AR hALA hARA hCover
    rw [hSourceCost]
    exact (Nat.add_le_add (Nat.add_le_add hCL hCR) hCB).trans hBudget.2
  by_cases hL0 : leftRows = ∅
  · have hAfter : ∀ p ∈ S \ K, lastRow < p := by
      intro p hp
      rcases hOutside p hp with hl | hr
      · have hh := (hLeftRows p).mpr ⟨(Finset.mem_sdiff.mp hp).1, hl⟩
        rw [hL0] at hh
        exact False.elim (Finset.notMem_empty _ hh)
      · exact hr
    cases chosenInterval
    · apply hEndpoint lastRow (hKS hLast) hLast true
      · intro p hp
        exact hAfter p (hA hp)
      · intro p hp
        exact hLeLast p (hB hp)
    · let q := (S \ K).min' hRestN
      have hq : q ∈ S \ K := Finset.min'_mem _ hRestN
      apply hEndpoint q (Finset.mem_sdiff.mp hq).1 hq false
      · intro p hp
        have hpl := hLeLast p (hA hp)
        have hlq := hAfter q hq
        change p < q
        omega
      · intro p hp
        exact Finset.min'_le (S \ K) p (hB hp)
  by_cases hR0 : rightRows = ∅
  · have hBefore : ∀ p ∈ S \ K, p < firstRow := by
      intro p hp
      rcases hOutside p hp with hl | hr
      · exact hl
      · have hh := (hRightRows p).mpr ⟨(Finset.mem_sdiff.mp hp).1, hr⟩
        rw [hR0] at hh
        exact False.elim (Finset.notMem_empty _ hh)
    cases chosenInterval
    · apply hEndpoint firstRow (hKS hFirst) hFirst false
      · intro p hp
        exact hBefore p (hA hp)
      · intro p hp
        exact hFirstLe p (hB hp)
    · let q := (S \ K).max' hRestN
      have hq : q ∈ S \ K := Finset.max'_mem _ hRestN
      apply hEndpoint q (Finset.mem_sdiff.mp hq).1 hq true
      · intro p hp
        have hfp := hFirstLe p (hA hp)
        have hqf := hBefore q hq
        change q < p
        omega
      · intro p hp
        exact Finset.le_max' (S \ K) p (hB hp)
  have hLN : leftRows.Nonempty := Finset.nonempty_iff_ne_empty.mpr hL0
  have hRN : rightRows.Nonempty := Finset.nonempty_iff_ne_empty.mpr hR0
  cases chosenInterval
  · exact hInternalOpposite rfl hLN hRN
  · exact hInternalChosen rfl hLN hRN

end ErdosSzekeres
