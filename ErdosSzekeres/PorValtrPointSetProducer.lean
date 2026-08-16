module

public import ErdosSzekeres.PorValtrSupportProduct
public import ErdosSzekeres.PorValtrCyclicSupportBridge

@[expose] public section

/-!
# The Pór--Valtr original-carrier point-set producer

This module extracts half of the cyclic support cells with large open pools
from the support-product estimate, then packages those pools on the original
carrier.
-/

namespace ErdosSzekeres

noncomputable section

private theorem porValtr_eight_mul_lt_supportDenominator
    (r : ℕ) (hr : 3 ≤ r) :
    8 * r < porValtrSupportDenominator r := by
  unfold porValtrSupportDenominator
  exact (show 8 * r < 32 * r by omega).trans
    (32 * r).lt_two_pow_self

private theorem porValtr_supportDenominator_mul_lowerBound_lt
    (N r : ℕ)
    (hlarge : porValtrSupportDenominator r < N) :
    porValtrSupportDenominator r * porValtrOpenPoolLowerBound N r < N := by
  let C := porValtrSupportDenominator r
  let d := (N + C - 1) / C
  have hCpos : 0 < C := by
    simp [C, porValtrSupportDenominator]
  have hlargeC : C < N := by
    simpa [C] using hlarge
  change C * (d - 1) < N
  have hdiv : d * C ≤ N + C - 1 := by
    dsimp [d]
    exact Nat.div_mul_le_self _ _
  by_cases hd : d = 0
  · simp [hd]
    omega
  · have hdOne : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have hsplit : C * (d - 1) + C = d * C := by
      calc
        C * (d - 1) + C = C * (d - 1) + C * 1 := by rw [Nat.mul_one]
        _ = C * ((d - 1) + 1) := (Nat.mul_add _ _ _).symm
        _ = C * d := by rw [Nat.sub_add_cancel hdOne]
        _ = d * C := Nat.mul_comm _ _
    omega

/-- If the Pór--Valtr support-product estimate holds, at least half of its
factors meet the exact ceiling-minus-one open-pool threshold. -/
theorem porValtr_exists_rich_half
    (N r : ℕ) (t : ℕ → ℕ)
    (hr : 3 ≤ r)
    (hlarge : porValtrSupportDenominator r < N)
    (hle : ∀ i, i < 2 * r → t i ≤ N)
    (hproduct :
      (N - 4 * r) ^ (2 * r) ≤
        porValtrSupportDenominator r ^ r *
          ∏ i ∈ Finset.range (2 * r), t i) :
    ∃ marked : Finset ℕ,
      marked ⊆ Finset.range (2 * r) ∧
      marked.card = r ∧
      ∀ i, i ∈ marked → porValtrOpenPoolLowerBound N r ≤ t i := by
  classical
  let C := porValtrSupportDenominator r
  let q := porValtrOpenPoolLowerBound N r
  let all := Finset.range (2 * r)
  let rich := all.filter fun i ↦ q ≤ t i
  by_cases hmany : r ≤ rich.card
  · obtain ⟨marked, hmarkedRich, hmarkedCard⟩ :=
      Finset.exists_subset_card_eq hmany
    refine ⟨marked, ?_, hmarkedCard, ?_⟩
    · intro i hi
      have hiData : i < 2 * r ∧ q ≤ t i := by
        simpa [rich, all] using hmarkedRich hi
      exact Finset.mem_range.mpr hiData.1
    · intro i hi
      have hiData : i < 2 * r ∧ q ≤ t i := by
        simpa [rich, all] using hmarkedRich hi
      simpa [q] using hiData.2
  · have hrichCard : rich.card < r := Nat.lt_of_not_ge hmany
    let low := all \ rich
    have hrichSubset : rich ⊆ all := by
      simp [rich]
    have hlowCardEq : low.card = all.card - rich.card := by
      simpa [low] using Finset.card_sdiff_of_subset hrichSubset
    have hallCard : all.card = 2 * r := by
      simp [all]
    have hlowCard : r ≤ low.card := by
      rw [hlowCardEq, hallCard]
      omega
    obtain ⟨small, hsmallLow, hsmallCard⟩ :=
      Finset.exists_subset_card_eq hlowCard
    have hlowSubset : low ⊆ all := by
      intro i hi
      have hi' : i ∈ all \ rich := by simpa [low] using hi
      exact (Finset.mem_sdiff.mp hi').1
    have hsmallAll : small ⊆ all := hsmallLow.trans hlowSubset
    have hqPos : 0 < q := by
      by_contra hq
      have hqZero : q = 0 := by omega
      have hrichEq : rich = all := by
        simp [rich, hqZero]
      rw [hrichEq, hallCard] at hrichCard
      omega
    have hsmallBound : ∀ i ∈ small, t i ≤ q - 1 := by
      intro i hi
      have hiLow : i ∈ all \ rich := by
        simpa [low] using hsmallLow hi
      have hiAll : i ∈ all := (Finset.mem_sdiff.mp hiLow).1
      have hiNotRich : i ∉ rich := (Finset.mem_sdiff.mp hiLow).2
      have hnot : ¬ q ≤ t i := by
        intro hqt
        apply hiNotRich
        change i ∈ all.filter (fun j : ℕ ↦ q ≤ t j)
        exact Finset.mem_filter.mpr ⟨hiAll, hqt⟩
      omega
    have hrestCard : (all \ small).card = r := by
      rw [Finset.card_sdiff_of_subset hsmallAll, hsmallCard, hallCard]
      omega
    have hrestBound : ∀ i ∈ all \ small, t i ≤ N := by
      intro i hi
      have hiAll : i ∈ all := (Finset.mem_sdiff.mp hi).1
      apply hle i
      simpa [all] using hiAll
    have hsmallProduct :
        ∏ i ∈ small, t i ≤ (q - 1) ^ r := by
      simpa [hsmallCard] using
        (Finset.prod_le_pow_card small t (q - 1) hsmallBound)
    have hrestProduct :
        ∏ i ∈ all \ small, t i ≤ N ^ r := by
      simpa [hrestCard] using
        (Finset.prod_le_pow_card (all \ small) t N hrestBound)
    have hallProductEq :
        (∏ i ∈ all, t i) =
          (∏ i ∈ small, t i) * ∏ i ∈ all \ small, t i := by
      calc
        (∏ i ∈ all, t i) =
            (∏ i ∈ all \ small, t i) * ∏ i ∈ small, t i :=
          (Finset.prod_sdiff hsmallAll).symm
        _ = (∏ i ∈ small, t i) * ∏ i ∈ all \ small, t i :=
          Nat.mul_comm _ _
    have hallProductBound :
        (∏ i ∈ all, t i) ≤ (q - 1) ^ r * N ^ r := by
      rw [hallProductEq]
      exact Nat.mul_le_mul hsmallProduct hrestProduct
    have hCgt : 8 * r < C := by
      simpa [C] using porValtr_eight_mul_lt_supportDenominator r hr
    have hCq : C * q < N := by
      simpa [C, q] using
        porValtr_supportDenominator_mul_lowerBound_lt N r hlarge
    have hqSplit : C * (q - 1) + C = C * q := by
      calc
        C * (q - 1) + C = C * (q - 1) + C * 1 := by rw [Nat.mul_one]
        _ = C * ((q - 1) + 1) := (Nat.mul_add _ _ _).symm
        _ = C * q := by rw [Nat.sub_add_cancel hqPos]
    have hgapAdd : C * (q - 1) + 8 * r < N := by
      calc
        C * (q - 1) + 8 * r < C * (q - 1) + C :=
          Nat.add_lt_add_left hCgt _
        _ = C * q := hqSplit
        _ < N := hCq
    have hN8 : 8 * r ≤ N := by omega
    have hgap : C * (q - 1) < N - 8 * r := by omega
    have hbaseLeft :
        C * (q - 1) * N < (N - 8 * r) * N :=
      Nat.mul_lt_mul_of_pos_right hgap (by omega)
    have hsquareGap : (N - 8 * r) * N < (N - 4 * r) ^ 2 := by
      calc
        (N - 8 * r) * N =
            (N - 8 * r) * ((N - 8 * r) + 8 * r) :=
          congrArg (fun x : ℕ ↦ (N - 8 * r) * x)
            (Nat.sub_add_cancel hN8).symm
        _ < ((N - 8 * r) + 4 * r) ^ 2 := by
          have hrPos : 0 < r := by omega
          have hrrPos : 0 < r * r := Nat.mul_pos hrPos hrPos
          nlinarith
        _ = (N - 4 * r) ^ 2 := by
          exact congrArg (fun x : ℕ ↦ x ^ 2) (by omega)
    have hbase : C * (q - 1) * N < (N - 4 * r) ^ 2 :=
      hbaseLeft.trans hsquareGap
    have hbasePow :
        (C * (q - 1) * N) ^ r < ((N - 4 * r) ^ 2) ^ r :=
      Nat.pow_lt_pow_left hbase (by omega)
    have hstrict :
        C ^ r * ((q - 1) ^ r * N ^ r) <
          (N - 4 * r) ^ (2 * r) := by
      calc
        C ^ r * ((q - 1) ^ r * N ^ r) =
            (C * (q - 1) * N) ^ r := by
          simp only [mul_pow, Nat.mul_assoc]
        _ < ((N - 4 * r) ^ 2) ^ r := hbasePow
        _ = (N - 4 * r) ^ (2 * r) := by rw [← pow_mul]
    have hproduct' :
        (N - 4 * r) ^ (2 * r) ≤
          C ^ r * ∏ i ∈ all, t i := by
      simpa [C, all] using hproduct
    have hscaledUpper :
        C ^ r * (∏ i ∈ all, t i) ≤
          C ^ r * ((q - 1) ^ r * N ^ r) :=
      Nat.mul_le_mul_left _ hallProductBound
    exact False.elim
      ((not_lt_of_ge (hproduct'.trans hscaledUpper)) hstrict)

/-- Every sufficiently large general-position point set supplies the exact
cyclic rich-pool data on the original carrier. -/
theorem exists_porValtrCyclicSupportData
    (P : Finset (Point 2)) (r : ℕ)
    (hr : 3 ≤ r)
    (hlarge : porValtrSupportDenominator r < P.card)
    (hgp : InGeneralPosition P) :
    ∃ data : PorValtrCyclicSupportData r
        (porValtrOpenPoolLowerBound P.card r),
      data.carrier = P := by
  classical
  obtain ⟨support⟩ := exists_porValtrSupportProductData P r hr hlarge hgp
  have hpoolSubset (i : ℕ) (hi : i < 2 * r) : support.sourcePool i ⊆ P := by
    rw [support.sourcePool_eq i hi]
    exact Finset.filter_subset _ _
  have hpoolCard (i : ℕ) (hi : i < 2 * r) :
      (support.sourcePool i).card ≤ P.card :=
    Finset.card_le_card (hpoolSubset i hi)
  obtain ⟨marked, hmarkedSubset, hmarkedCard, hmarkedRich⟩ :=
    porValtr_exists_rich_half P.card r
      (fun i ↦ (support.sourcePool i).card)
      hr hlarge hpoolCard support.productBound
  let data : PorValtrCyclicSupportData r
      (porValtrOpenPoolLowerBound P.card r) := {
    anchors := support.anchors
    carrier := P
    marked := marked
    sourcePool := support.sourcePool
    strictCap := support.strictCap
    markedSubset := hmarkedSubset
    markedCard := hmarkedCard
    anchorsSubset := by
      intro i hi
      exact support.anchorsSubset i hi
    sourcePoolSubset := by
      intro i hi
      exact hpoolSubset i (Finset.mem_range.mp (hmarkedSubset hi))
    sourcePoolsDisjoint := by
      intro i hi j hj hij
      exact support.sourcePoolsDisjoint
        i (Finset.mem_range.mp (hmarkedSubset hi))
        j (Finset.mem_range.mp (hmarkedSubset hj)) hij
    generalPosition := hgp
    sourceCard := hmarkedRich
    sourceRegion := by
      intro i hi hiPos p hp
      have hiRange : i < 2 * r :=
        Finset.mem_range.mp (hmarkedSubset hi)
      rw [support.sourcePool_eq i hiRange] at hp
      change p ∈ P.filter
        (fun p ↦ p ∈ porValtrCyclicOpenCell (2 * r) support.anchors i) at hp
      have hpCell :
          p ∈ porValtrCyclicOpenCell (2 * r) support.anchors i :=
        (Finset.mem_filter.mp hp).2
      simpa [porValtrCyclicOpenCell, Nat.ne_of_gt hiPos] using hpCell
  }
  exact ⟨data, rfl⟩

end

end ErdosSzekeres

end
