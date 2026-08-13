module

public import ErdosSzekeres.StructuralChargingCarrierOnlyMixedNormalForm567
public import Mathlib.Tactic

@[expose] public section

/-!
# Label and carrier extraction for the mixed state-567 normal form

This module deliberately stops before reconstructing any of the six witnesses.
It packages one short-first normal form into a single injection of the twelve
canonical labels, so the three witness-pair proofs can elaborate independently.
-/

namespace ErdosSzekeres

/-- A monochromatic polygon supported on an unordered finite vertex set. -/
def IsTurnPolygonSet {n : ℕ} (χ : TripleColoring n)
    (vertices : Finset (Fin n)) (turn : Turn) : Prop :=
  ∀ ⦃i j k : Fin n⦄ (hij : i < j) (hjk : j < k),
    i ∈ vertices → j ∈ vertices → k ∈ vertices →
      χ ⟨i, j, k, hij, hjk⟩ = turn

/-- A finite ambient set contains a monochromatic polygon of the given size. -/
def ContainsTurnPolygonSet {n : ℕ} (χ : TripleColoring n)
    (ambient : Finset (Fin n)) (turn : Turn) (cardinality : ℕ) : Prop :=
  ∃ vertices ⊆ ambient,
    vertices.card = cardinality ∧ IsTurnPolygonSet χ vertices turn

/-- The exact cap-five, cup-six, or strong-seven target of encoding A. -/
def ContainsTarget567 {n : ℕ} (χ : TripleColoring n)
    (ambient : Finset (Fin n)) : Prop :=
  ContainsTurnPolygonSet χ ambient .right 5 ∨
    ContainsTurnPolygonSet χ ambient .left 6 ∨
    ContainsStrongPolygonSet χ ambient 7

def mixed567A0 : Finset (Fin 12) := {0, 7, 8, 9, 10, 11}
def mixed567A1 : Finset (Fin 12) := {1, 6, 8, 9, 10, 11}
def mixed567B0 : Finset (Fin 12) := {1, 2, 3, 4, 5, 7}
def mixed567B1 : Finset (Fin 12) := {0, 2, 3, 4, 5, 6}
def mixed567D0 : Finset (Fin 12) := {0, 1, 4, 5, 6, 7}
def mixed567D1 : Finset (Fin 12) := {0, 1, 2, 3, 6, 7}

/-- The precise arbitrary-placement finite theorem supplied by encoding A. -/
def Mixed567FiniteTheorem : Prop :=
  ∀ {n : ℕ} (χ : TripleColoring n) (embed : Fin 12 ↪ Fin n),
    OneChangeOn χ (Finset.univ.image embed) →
    IsStrongPolygonSet χ (mixed567A0.image embed) →
    IsStrongPolygonSet χ (mixed567A1.image embed) →
    IsStrongPolygonSet χ (mixed567B0.image embed) →
    IsStrongPolygonSet χ (mixed567B1.image embed) →
    IsStrongPolygonSet χ (mixed567D0.image embed) →
    IsStrongPolygonSet χ (mixed567D1.image embed) →
    ContainsTarget567 χ (Finset.univ.image embed)

/-- An explicit twelve-label realization of a mixed omission normal form. -/
structure Mixed567Labelling {n : ℕ}
    (first second : Finset (Fin n))
    (witnesses : Finset (Finset (Fin n))) where
  embed : Fin 12 ↪ Fin n
  carrier_image : Finset.univ.image embed = first ∪ second
  A0_mem : mixed567A0.image embed ∈ witnesses
  A1_mem : mixed567A1.image embed ∈ witnesses
  B0_mem : mixed567B0.image embed ∈ witnesses
  B1_mem : mixed567B1.image embed ∈ witnesses
  D0_mem : mixed567D0.image embed ∈ witnesses
  D1_mem : mixed567D1.image embed ∈ witnesses

def mixed567Map {n : ℕ}
    (p q u0 u1 v0 v1 c d e0 e1 e2 e3 : Fin n) : Fin 12 → Fin n :=
  ![p, q, u0, u1, v0, v1, c, d, e0, e1, e2, e3]

theorem image_mixed567Map {n : ℕ}
    (p q u0 u1 v0 v1 c d e0 e1 e2 e3 : Fin n) :
    Finset.univ.image (mixed567Map p q u0 u1 v0 v1 c d e0 e1 e2 e3) =
      {p, q, u0, u1, v0, v1, c, d, e0, e1, e2, e3} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [mixed567Map]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, by simp [mixed567Map]⟩
    · exact ⟨1, by simp [mixed567Map]⟩
    · exact ⟨2, by simp [mixed567Map]⟩
    · exact ⟨3, by simp [mixed567Map]⟩
    · exact ⟨4, by simp [mixed567Map]⟩
    · exact ⟨5, by simp [mixed567Map]⟩
    · exact ⟨6, by simp [mixed567Map]⟩
    · exact ⟨7, by simp [mixed567Map]⟩
    · exact ⟨8, by simp [mixed567Map]⟩
    · exact ⟨9, by simp [mixed567Map]⟩
    · exact ⟨10, by simp [mixed567Map]⟩
    · exact ⟨11, by simp [mixed567Map]⟩

private theorem carrier_reconstruct_left {n : ℕ}
    {first P Q : Finset (Fin n)} {p q : Fin n}
    (hp : p ∈ first) (hq : q ∈ first) (hpq : p ≠ q)
    (hPQ : P ∪ Q = (first.erase p).erase q) :
    {p, q} ∪ (P ∪ Q) = first := by
  ext x
  rw [hPQ]
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase]
  constructor
  · rintro ((rfl | rfl) | ⟨_, _, hx⟩)
    · exact hp
    · exact hq
    · exact hx
  · intro hx
    by_cases hxp : x = p
    · exact Or.inl (Or.inl hxp)
    by_cases hxq : x = q
    · exact Or.inl (Or.inr hxq)
    exact Or.inr ⟨hxq, hxp, hx⟩

private theorem carrier_reconstruct_right {n : ℕ}
    {second : Finset (Fin n)} {c d : Fin n}
    (hc : c ∈ second) (hd : d ∈ second) (hcd : c ≠ d) :
    {c, d} ∪ (second.erase c).erase d = second := by
  simpa [Finset.union_comm] using
    carrier_reconstruct_left (first := second) hc hd hcd
      (P := (second.erase c).erase d) (Q := ∅) (by simp)

private theorem mixed567_union_first_labels {α : Type*} [DecidableEq α]
    (p q u0 u1 v0 v1 : α) :
    ({p, q, u0, u1, v0, v1} : Finset α) =
      {p, q} ∪ ({u0, u1} ∪ {v0, v1}) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  tauto

private theorem mixed567_union_second_labels {α : Type*} [DecidableEq α]
    (c d e0 e1 e2 e3 : α) :
    ({c, d, e0, e1, e2, e3} : Finset α) =
      {c, d} ∪ {e0, e1, e2, e3} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  tauto

private theorem mixed567_union_all_labels {α : Type*} [DecidableEq α]
    (p q u0 u1 v0 v1 c d e0 e1 e2 e3 : α) :
    ({p, q, u0, u1, v0, v1, c, d, e0, e1, e2, e3} : Finset α) =
      {p, q, u0, u1, v0, v1} ∪ {c, d, e0, e1, e2, e3} := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  tauto

/-- All data shared by the three independent witness-pair reconstructions. -/
structure Mixed567ShortFirstData {n : ℕ}
    (first second : Finset (Fin n))
    (witnesses : Finset (Finset (Fin n))) where
  p : Fin n
  q : Fin n
  u0 : Fin n
  u1 : Fin n
  v0 : Fin n
  v1 : Fin n
  c : Fin n
  d : Fin n
  e0 : Fin n
  e1 : Fin n
  e2 : Fin n
  e3 : Fin n
  P : Finset (Fin n)
  Q : Finset (Fin n)
  A0 : Finset (Fin n)
  A1 : Finset (Fin n)
  B0 : Finset (Fin n)
  B1 : Finset (Fin n)
  D0 : Finset (Fin n)
  D1 : Finset (Fin n)
  hp : p ∈ first
  hq : q ∈ first
  hc : c ∈ second
  hd : d ∈ second
  hpq : p ≠ q
  hcd : c ≠ d
  hPQDisjoint : Disjoint P Q
  hPQ : P ∪ Q = (first.erase p).erase q
  hP : P = {u0, u1}
  hQ : Q = {v0, v1}
  hE : (second.erase c).erase d = {e0, e1, e2, e3}
  hwitnesses : witnesses = {A0, A1, B0, B1, D0, D1}
  hA0First : first \ A0 = first.erase p
  hA0Second : second \ A0 = {c}
  hA1First : first \ A1 = first.erase q
  hA1Second : second \ A1 = {d}
  hB0First : first \ B0 = {p}
  hB0Second : second \ B0 = second.erase d
  hB1First : first \ B1 = {q}
  hB1Second : second \ B1 = second.erase c
  hD0First : first \ D0 = P
  hD0Second : second \ D0 = (second.erase c).erase d
  hD1First : first \ D1 = Q
  hD1Second : second \ D1 = (second.erase c).erase d
  hinjective : Function.Injective
    (mixed567Map p q u0 u1 v0 v1 c d e0 e1 e2 e3)
  carrier_image :
    Finset.univ.image (mixed567Map p q u0 u1 v0 v1 c d e0 e1 e2 e3) =
      first ∪ second
  A0_mem : A0 ∈ witnesses
  A1_mem : A1 ∈ witnesses
  B0_mem : B0 ∈ witnesses
  B1_mem : B1 ∈ witnesses
  D0_mem : D0 ∈ witnesses
  D1_mem : D1 ∈ witnesses

def Mixed567ShortFirstData.embed {n : ℕ}
    {first second : Finset (Fin n)} {witnesses : Finset (Finset (Fin n))}
    (data : Mixed567ShortFirstData first second witnesses) : Fin 12 ↪ Fin n :=
  ⟨mixed567Map data.p data.q data.u0 data.u1 data.v0 data.v1
    data.c data.d data.e0 data.e1 data.e2 data.e3, data.hinjective⟩

/-- Extract the canonical labels and prove injection/carrier coverage only. -/
theorem shortFirstMixed567Data {n : ℕ}
    {first second : Finset (Fin n)}
    {witnesses : Finset (Finset (Fin n))}
    (hfirstCard : first.card = 6) (hsecondCard : second.card = 6)
    (hcarrierDisjoint : Disjoint first second)
    (hnormal : IsShortFirstMixedOmissionNormalForm567 first second witnesses) :
    Nonempty (Mixed567ShortFirstData first second witnesses) := by
  classical
  rcases hnormal with
    ⟨p, q, c, d, P, Q, A0, A1, B0, B1, D0, D1,
      hp, hq, hc, hd, hpq, hcd, hPCard, hQCard, hPQDisjoint, hPQ,
      hwitnesses, _hexplicitCard, hA0First, hA0Second, hA1First, hA1Second,
      hB0First, hB0Second, hB1First, hB1Second, hD0First, hD0Second,
      hD1First, hD1Second⟩
  obtain ⟨u0, u1, _hu01, hP⟩ := Finset.card_eq_two.mp hPCard
  obtain ⟨v0, v1, _hv01, hQ⟩ := Finset.card_eq_two.mp hQCard
  have hECard : ((second.erase c).erase d).card = 4 := by
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hcd.symm, hd⟩),
      Finset.card_erase_of_mem hc, hsecondCard]
  obtain ⟨e0, e1, e2, e3, _he01, _he02, _he03, _he12, _he13, _he23, hE⟩ :=
    Finset.card_eq_four.mp hECard
  have hFirst : {p, q, u0, u1, v0, v1} = first := by
    calc
      {p, q, u0, u1, v0, v1} = {p, q} ∪ (P ∪ Q) := by
        rw [hP, hQ]
        exact mixed567_union_first_labels p q u0 u1 v0 v1
      _ = first := carrier_reconstruct_left hp hq hpq hPQ
  have hSecond : {c, d, e0, e1, e2, e3} = second := by
    calc
      {c, d, e0, e1, e2, e3} = {c, d} ∪ (second.erase c).erase d := by
        rw [hE]
        exact mixed567_union_second_labels c d e0 e1 e2 e3
      _ = second := carrier_reconstruct_right hc hd hcd
  let raw := mixed567Map p q u0 u1 v0 v1 c d e0 e1 e2 e3
  have himage : Finset.univ.image raw = first ∪ second := by
    rw [show Finset.univ.image raw =
        {p, q, u0, u1, v0, v1, c, d, e0, e1, e2, e3} by
      simpa [raw] using image_mixed567Map p q u0 u1 v0 v1 c d e0 e1 e2 e3]
    rw [← hFirst, ← hSecond]
    exact mixed567_union_all_labels p q u0 u1 v0 v1 c d e0 e1 e2 e3
  have himageCard : (Finset.univ.image raw).card =
      (Finset.univ : Finset (Fin 12)).card := by
    rw [himage, Finset.card_union_of_disjoint hcarrierDisjoint,
      hfirstCard, hsecondCard]
    norm_num
  have hinjOn : Set.InjOn raw (Finset.univ : Finset (Fin 12)) :=
    Finset.card_image_iff.mp himageCard
  have hinjective : Function.Injective raw := by
    intro i j hij
    exact hinjOn (by simp) (by simp) hij
  have hA0Mem : A0 ∈ witnesses := by rw [hwitnesses]; simp
  have hA1Mem : A1 ∈ witnesses := by rw [hwitnesses]; simp
  have hB0Mem : B0 ∈ witnesses := by rw [hwitnesses]; simp
  have hB1Mem : B1 ∈ witnesses := by rw [hwitnesses]; simp
  have hD0Mem : D0 ∈ witnesses := by rw [hwitnesses]; simp
  have hD1Mem : D1 ∈ witnesses := by rw [hwitnesses]; simp
  refine ⟨{
    p := p, q := q, u0 := u0, u1 := u1, v0 := v0, v1 := v1,
    c := c, d := d, e0 := e0, e1 := e1, e2 := e2, e3 := e3,
    P := P, Q := Q, A0 := A0, A1 := A1, B0 := B0, B1 := B1,
    D0 := D0, D1 := D1,
    hp := hp, hq := hq, hc := hc, hd := hd, hpq := hpq, hcd := hcd,
    hPQDisjoint := hPQDisjoint, hPQ := hPQ, hP := hP, hQ := hQ,
    hE := hE, hwitnesses := hwitnesses,
    hA0First := hA0First, hA0Second := hA0Second,
    hA1First := hA1First, hA1Second := hA1Second,
    hB0First := hB0First, hB0Second := hB0Second,
    hB1First := hB1First, hB1Second := hB1Second,
    hD0First := hD0First, hD0Second := hD0Second,
    hD1First := hD1First, hD1Second := hD1Second,
    hinjective := hinjective, carrier_image := by simpa [raw] using himage,
    A0_mem := hA0Mem, A1_mem := hA1Mem, B0_mem := hB0Mem,
    B1_mem := hB1Mem, D0_mem := hD0Mem, D1_mem := hD1Mem }⟩

end ErdosSzekeres

end
