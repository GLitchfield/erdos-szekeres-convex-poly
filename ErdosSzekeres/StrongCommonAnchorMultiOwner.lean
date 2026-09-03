module

public import ErdosSzekeres.StructuralCharging

@[expose] public section

/-!
# Common-anchor multi-owner normal forms

This file isolates the literal `TurnSequenceAllowed` calculations behind the
two-owner perfect-matching localization used by the common-anchor route.
-/

namespace ErdosSzekeres

/-- The first perfect matching on four named vertices. -/
def IsBaseMatching0
    (e01 e02 e03 e12 e13 e23 : Prop) : Prop :=
  e01 ∧ e23 ∧ ¬e02 ∧ ¬e03 ∧ ¬e12 ∧ ¬e13

/-- The second perfect matching on four named vertices. -/
def IsBaseMatching1
    (e01 e02 e03 e12 e13 e23 : Prop) : Prop :=
  e02 ∧ e13 ∧ ¬e01 ∧ ¬e03 ∧ ¬e12 ∧ ¬e23

/-- The third perfect matching on four named vertices. -/
def IsBaseMatching2
    (e01 e02 e03 e12 e13 e23 : Prop) : Prop :=
  e03 ∧ e12 ∧ ¬e01 ∧ ¬e02 ∧ ¬e13 ∧ ¬e23

/-- A six-edge graph on four named vertices is one of the three perfect matchings. -/
def IsBasePerfectMatching
    (e01 e02 e03 e12 e13 e23 : Prop) : Prop :=
  IsBaseMatching0 e01 e02 e03 e12 e13 e23 ∨
    IsBaseMatching1 e01 e02 e03 e12 e13 e23 ∨
      IsBaseMatching2 e01 e02 e03 e12 e13 e23

/-- In an allowed word with an equal first pair and an unequal last pair,
the first three entries agree. -/
theorem TurnSequenceAllowed.eq_first_of_first_eq_of_last_ne
    {A B C D : Turn} (h : TurnSequenceAllowed A B C D)
    (hab : A = B) (hcd : C ≠ D) : A = C := by
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

/-- In an allowed word with an unequal first pair and an equal last pair,
the last three entries agree. -/
theorem TurnSequenceAllowed.eq_last_of_first_ne_of_last_eq
    {A B C D : Turn} (h : TurnSequenceAllowed A B C D)
    (hab : A ≠ B) (hcd : C = D) : B = D := by
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

/-- Reversing an allowed four-turn word preserves allowedness. -/
theorem TurnSequenceAllowed.reverse
    {A B C D : Turn} (h : TurnSequenceAllowed A B C D) :
    TurnSequenceAllowed D C B A := by
  rcases h with h | h | h | h | h | h | h | h <;>
    simp_all [TurnSequenceAllowed]

/-- Normal form when both owners lie above the four ordered base vertices. -/
theorem perfectMatching_sameRight_normalForm
    {L R alpha beta z0 z1 z2 z3 : Turn}
    (h01 : TurnSequenceAllowed L L z0 z1)
    (h02 : TurnSequenceAllowed R R z0 z2)
    (h12 : TurnSequenceAllowed R R z1 z2)
    (h03 : TurnSequenceAllowed alpha beta z0 z3)
    (h13 : TurnSequenceAllowed alpha beta z1 z3)
    (h23 : TurnSequenceAllowed alpha beta z2 z3)
    (hmatching : IsBasePerfectMatching
      (z0 = z1) (z0 = z2) (alpha = beta ∧ z0 = z3)
      (z1 = z2) (alpha = beta ∧ z1 = z3)
      (alpha = beta ∧ z2 = z3)) :
    (IsBaseMatching0
        (z0 = z1) (z0 = z2) (alpha = beta ∧ z0 = z3)
        (z1 = z2) (alpha = beta ∧ z1 = z3)
        (alpha = beta ∧ z2 = z3) ∧
      alpha = beta ∧ alpha = R) ∨
    (IsBaseMatching1
        (z0 = z1) (z0 = z2) (alpha = beta ∧ z0 = z3)
        (z1 = z2) (alpha = beta ∧ z1 = z3)
        (alpha = beta ∧ z2 = z3) ∧
      alpha = beta ∧ alpha = L ∧ L ≠ R) ∨
    (IsBaseMatching2
        (z0 = z1) (z0 = z2) (alpha = beta ∧ z0 = z3)
        (z1 = z2) (alpha = beta ∧ z1 = z3)
        (alpha = beta ∧ z2 = z3) ∧
      alpha = beta ∧ L = R ∧ L ≠ alpha) := by
  rcases hmatching with hm | hm | hm
  · left
    refine ⟨hm, ?_⟩
    rcases hm with ⟨_, h23e, hn02, hn03, _, _⟩
    obtain ⟨hab, hz23⟩ := h23e
    have hz02 : z0 ≠ z2 := hn02
    have hz03 : z0 ≠ z3 := by
      intro hz
      exact hn03 ⟨hab, hz⟩
    have hR : R = z0 := h02.eq_first_of_first_eq_of_last_ne rfl hz02
    have ha : alpha = z0 := by
      rw [← hab] at h03
      exact h03.eq_first_of_first_eq_of_last_ne rfl hz03
    exact ⟨hab, ha.trans hR.symm⟩
  · right
    left
    refine ⟨hm, ?_⟩
    rcases hm with ⟨_, h13e, hn01, hn03, hn12, _⟩
    obtain ⟨hab, hz13⟩ := h13e
    have hz01 : z0 ≠ z1 := hn01
    have hz12 : z1 ≠ z2 := hn12
    have hz03 : z0 ≠ z3 := by
      intro hz
      exact hn03 ⟨hab, hz⟩
    have hL : L = z0 := h01.eq_first_of_first_eq_of_last_ne rfl hz01
    have hR : R = z1 := h12.eq_first_of_first_eq_of_last_ne rfl hz12
    have ha : alpha = z0 := by
      rw [← hab] at h03
      exact h03.eq_first_of_first_eq_of_last_ne rfl hz03
    refine ⟨hab, ha.trans hL.symm, ?_⟩
    intro hLR
    exact hz01 (hL.symm.trans (hLR.trans hR))
  · right
    right
    refine ⟨hm, ?_⟩
    rcases hm with ⟨h03e, h12e, hn01, hn02, hn13, _⟩
    obtain ⟨hab, hz03⟩ := h03e
    have hz01 : z0 ≠ z1 := hn01
    have hz02 : z0 ≠ z2 := hn02
    have hz13 : z1 ≠ z3 := by
      intro hz
      exact hn13 ⟨hab, hz⟩
    have hL : L = z0 := h01.eq_first_of_first_eq_of_last_ne rfl hz01
    have hR : R = z0 := h02.eq_first_of_first_eq_of_last_ne rfl hz02
    have ha : alpha = z1 := by
      rw [← hab] at h13
      exact h13.eq_first_of_first_eq_of_last_ne rfl hz13
    refine ⟨hab, hL.trans hR.symm, ?_⟩
    intro hLa
    exact hz01 (hL.symm.trans (hLa.trans ha))

/-- Order-dual normal form when both owners lie below the four ordered base
vertices.  This is obtained by reversing the six literal one-change words;
it does not reverse the ambient order embedding. -/
theorem perfectMatching_sameLeft_normalForm
    {L R alpha beta z0 z1 z2 z3 : Turn}
    (h01 : TurnSequenceAllowed z0 z1 alpha beta)
    (h02 : TurnSequenceAllowed z0 z2 alpha beta)
    (h03 : TurnSequenceAllowed z0 z3 alpha beta)
    (h12 : TurnSequenceAllowed z1 z2 L L)
    (h13 : TurnSequenceAllowed z1 z3 L L)
    (h23 : TurnSequenceAllowed z2 z3 R R)
    (hmatching : IsBasePerfectMatching
      (alpha = beta ∧ z0 = z1) (alpha = beta ∧ z0 = z2)
      (alpha = beta ∧ z0 = z3) (z1 = z2) (z1 = z3) (z2 = z3)) :
    (IsBaseMatching0
        (alpha = beta ∧ z0 = z1) (alpha = beta ∧ z0 = z2)
        (alpha = beta ∧ z0 = z3) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = beta ∧ alpha = L) ∨
    (IsBaseMatching1
        (alpha = beta ∧ z0 = z1) (alpha = beta ∧ z0 = z2)
        (alpha = beta ∧ z0 = z3) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = beta ∧ alpha = R ∧ R ≠ L) ∨
    (IsBaseMatching2
        (alpha = beta ∧ z0 = z1) (alpha = beta ∧ z0 = z2)
        (alpha = beta ∧ z0 = z3) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = beta ∧ L = R ∧ L ≠ alpha) := by
  have hmrev : IsBasePerfectMatching
      (z3 = z2) (z3 = z1) (beta = alpha ∧ z3 = z0)
      (z2 = z1) (beta = alpha ∧ z2 = z0)
      (beta = alpha ∧ z1 = z0) := by
    simpa [IsBasePerfectMatching, IsBaseMatching0, IsBaseMatching1,
      IsBaseMatching2, eq_comm, and_comm, and_left_comm, and_assoc] using hmatching
  have hnormal := perfectMatching_sameRight_normalForm
    (L := R) (R := L) (alpha := beta) (beta := alpha)
    (z0 := z3) (z1 := z2) (z2 := z1) (z3 := z0)
    h23.reverse h13.reverse h12.reverse h03.reverse h02.reverse h01.reverse hmrev
  rcases hnormal with h0 | h1 | h2
  · rcases h0 with ⟨hm, hba, hbL⟩
    left
    refine ⟨?_, hba.symm, hba.symm.trans hbL⟩
    simpa [IsBaseMatching0, eq_comm, and_comm, and_left_comm, and_assoc] using hm
  · rcases h1 with ⟨hm, hba, hbR, hRL⟩
    right
    left
    refine ⟨?_, hba.symm, hba.symm.trans hbR, hRL⟩
    simpa [IsBaseMatching1, eq_comm, and_comm, and_left_comm, and_assoc] using hm
  · rcases h2 with ⟨hm, hba, hRL, hRbeta⟩
    right
    right
    refine ⟨?_, hba.symm, hRL.symm, ?_⟩
    · simpa [IsBaseMatching2, eq_comm, and_comm, and_left_comm, and_assoc] using hm
    · intro hLalpha
      exact hRbeta (hRL.trans (hLalpha.trans hba.symm))

/-- Normal form when both owners lie in the first internal base gap. -/
theorem perfectMatching_sameFirstGap_normalForm
    {L R alpha beta z0 z1 z2 z3 : Turn}
    (h01 : TurnSequenceAllowed z0 alpha beta z1)
    (h02 : TurnSequenceAllowed z0 alpha beta z2)
    (h03 : TurnSequenceAllowed z0 alpha beta z3)
    (h12 : TurnSequenceAllowed z1 z2 L L)
    (h13 : TurnSequenceAllowed z1 z3 L L)
    (h23 : TurnSequenceAllowed z2 z3 R R)
    (hmatching : IsBasePerfectMatching
      (z0 = alpha ∧ beta = z1) (z0 = alpha ∧ beta = z2)
      (z0 = alpha ∧ beta = z3) (z1 = z2) (z1 = z3) (z2 = z3)) :
    (IsBaseMatching0
        (z0 = alpha ∧ beta = z1) (z0 = alpha ∧ beta = z2)
        (z0 = alpha ∧ beta = z3) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = beta ∧ alpha ≠ L) ∨
    (IsBaseMatching1
        (z0 = alpha ∧ beta = z1) (z0 = alpha ∧ beta = z2)
        (z0 = alpha ∧ beta = z3) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = beta ∧ alpha = L ∧ L ≠ R) ∨
    (IsBaseMatching2
        (z0 = alpha ∧ beta = z1) (z0 = alpha ∧ beta = z2)
        (z0 = alpha ∧ beta = z3) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = beta ∧ alpha = L ∧ L = R) := by
  rcases hmatching with hm | hm | hm
  · left
    refine ⟨hm, ?_⟩
    rcases hm with ⟨h01e, h23e, hn02, _, hn12, _⟩
    obtain ⟨hz0, hbz1⟩ := h01e
    have hbz2 : beta ≠ z2 := by
      intro hb
      exact hn02 ⟨hz0, hb⟩
    have hab : alpha = beta := by
      exact hz0.symm.trans (h02.eq_first_of_first_eq_of_last_ne hz0 hbz2)
    have hz12 : z1 ≠ z2 := hn12
    have hz2L : z2 = L := h12.eq_last_of_first_ne_of_last_eq hz12 rfl
    refine ⟨hab, ?_⟩
    intro haL
    exact hz12 (hbz1.symm.trans (hab.symm.trans (haL.trans hz2L.symm)))
  · right
    left
    refine ⟨hm, ?_⟩
    rcases hm with ⟨h02e, h13e, hn01, _, hn12, hn23⟩
    obtain ⟨hz0, hbz2⟩ := h02e
    have hbz1 : beta ≠ z1 := by
      intro hb
      exact hn01 ⟨hz0, hb⟩
    have hab : alpha = beta :=
      hz0.symm.trans (h01.eq_first_of_first_eq_of_last_ne hz0 hbz1)
    have hz12 : z1 ≠ z2 := hn12
    have hz2L : z2 = L := h12.eq_last_of_first_ne_of_last_eq hz12 rfl
    have hz23 : z2 ≠ z3 := hn23
    have hz3R : z3 = R := h23.eq_last_of_first_ne_of_last_eq hz23 rfl
    refine ⟨hab, hab.trans (hbz2.trans hz2L), ?_⟩
    intro hLR
    exact hz23 (hz2L.trans (hLR.trans hz3R.symm))
  · right
    right
    refine ⟨hm, ?_⟩
    rcases hm with ⟨h03e, h12e, hn01, _, hn13, hn23⟩
    obtain ⟨hz0, hbz3⟩ := h03e
    have hbz1 : beta ≠ z1 := by
      intro hb
      exact hn01 ⟨hz0, hb⟩
    have hab : alpha = beta :=
      hz0.symm.trans (h01.eq_first_of_first_eq_of_last_ne hz0 hbz1)
    have hz13 : z1 ≠ z3 := hn13
    have hz3L : z3 = L := h13.eq_last_of_first_ne_of_last_eq hz13 rfl
    have hz23 : z2 ≠ z3 := hn23
    have hz3R : z3 = R := h23.eq_last_of_first_ne_of_last_eq hz23 rfl
    exact ⟨hab, hab.trans (hbz3.trans hz3L), hz3L.symm.trans hz3R⟩

/-- Normal form for owners in the two consecutive left sweep gaps. -/
theorem perfectMatching_leftAdjacent_normalForm
    {L R alpha beta z0 z1 z2 z3 : Turn}
    (h01 : TurnSequenceAllowed z0 alpha z1 beta)
    (h02 : TurnSequenceAllowed z0 alpha z2 beta)
    (h03 : TurnSequenceAllowed z0 alpha z3 beta)
    (h12 : TurnSequenceAllowed z1 z2 L L)
    (h13 : TurnSequenceAllowed z1 z3 L L)
    (h23 : TurnSequenceAllowed z2 z3 R R)
    (hmatching : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = beta) (z0 = alpha ∧ z2 = beta)
      (z0 = alpha ∧ z3 = beta) (z1 = z2) (z1 = z3) (z2 = z3)) :
    (IsBaseMatching0
        (z0 = alpha ∧ z1 = beta) (z0 = alpha ∧ z2 = beta)
        (z0 = alpha ∧ z3 = beta) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = L ∧ beta ≠ L) ∨
    (IsBaseMatching1
        (z0 = alpha ∧ z1 = beta) (z0 = alpha ∧ z2 = beta)
        (z0 = alpha ∧ z3 = beta) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      alpha = R ∧ R ≠ L ∧ beta = L) ∨
    (IsBaseMatching2
        (z0 = alpha ∧ z1 = beta) (z0 = alpha ∧ z2 = beta)
        (z0 = alpha ∧ z3 = beta) (z1 = z2) (z1 = z3) (z2 = z3) ∧
      L = R ∧ beta = L ∧ alpha ≠ L) := by
  rcases hmatching with hm | hm | hm
  · left
    refine ⟨hm, ?_⟩
    rcases hm with ⟨h01e, h23e, hn02, _, hn12, _⟩
    obtain ⟨hz0, hz1⟩ := h01e
    have hz2b : z2 ≠ beta := by
      intro hb
      exact hn02 ⟨hz0, hb⟩
    have haz2 : alpha = z2 :=
      hz0.symm.trans (h02.eq_first_of_first_eq_of_last_ne hz0 hz2b)
    have hz12 : z1 ≠ z2 := hn12
    have hz2L : z2 = L := h12.eq_last_of_first_ne_of_last_eq hz12 rfl
    refine ⟨haz2.trans hz2L, ?_⟩
    intro hbL
    exact hz12 (hz1.trans (hbL.trans hz2L.symm))
  · right
    left
    refine ⟨hm, ?_⟩
    rcases hm with ⟨h02e, h13e, hn01, _, hn12, hn23⟩
    obtain ⟨hz0, hz2⟩ := h02e
    have hz1b : z1 ≠ beta := by
      intro hb
      exact hn01 ⟨hz0, hb⟩
    have haz1 : alpha = z1 :=
      hz0.symm.trans (h01.eq_first_of_first_eq_of_last_ne hz0 hz1b)
    have hz12 : z1 ≠ z2 := hn12
    have hz2L : z2 = L := h12.eq_last_of_first_ne_of_last_eq hz12 rfl
    have hz23 : z2 ≠ z3 := hn23
    have hz3R : z3 = R := h23.eq_last_of_first_ne_of_last_eq hz23 rfl
    refine ⟨haz1.trans (h13e.trans hz3R), ?_, hz2.symm.trans hz2L⟩
    intro hRL
    exact hz23 (hz2L.trans (hRL.symm.trans hz3R.symm))
  · right
    right
    refine ⟨hm, ?_⟩
    rcases hm with ⟨h03e, h12e, hn01, _, hn13, hn23⟩
    obtain ⟨hz0, hz3⟩ := h03e
    have hz1b : z1 ≠ beta := by
      intro hb
      exact hn01 ⟨hz0, hb⟩
    have haz1 : alpha = z1 :=
      hz0.symm.trans (h01.eq_first_of_first_eq_of_last_ne hz0 hz1b)
    have hz13 : z1 ≠ z3 := hn13
    have hz3L : z3 = L := h13.eq_last_of_first_ne_of_last_eq hz13 rfl
    have hz23 : z2 ≠ z3 := hn23
    have hz3R : z3 = R := h23.eq_last_of_first_ne_of_last_eq hz23 rfl
    refine ⟨hz3L.symm.trans hz3R, hz3.symm.trans hz3L, ?_⟩
    intro haL
    exact hz13 (haz1.symm.trans (haL.trans hz3L.symm))

/-- The common edge pattern for gap pairs `02` and `12` can only be `M0`. -/
theorem perfectMatching_middleGap_pattern
    {P Q R S : Prop}
    (hmatching : IsBasePerfectMatching
      (P ∧ Q) (P ∧ R) (P ∧ S) (Q ∧ R) (Q ∧ S) (R ↔ S)) :
    IsBaseMatching0
      (P ∧ Q) (P ∧ R) (P ∧ S) (Q ∧ R) (Q ∧ S) (R ↔ S) := by
  rcases hmatching with hm | hm | hm
  · exact hm
  · rcases hm with ⟨⟨hP, hR⟩, ⟨hQ, hS⟩, _, _, _, hnRS⟩
    exact (hnRS ⟨fun _ ↦ hS, fun _ ↦ hR⟩).elim
  · rcases hm with ⟨⟨hP, hS⟩, ⟨hQ, hR⟩, _, _, _, hnRS⟩
    exact (hnRS ⟨fun _ ↦ hS, fun _ ↦ hR⟩).elim

/-- In placement `02`, the unique matching forces the gap-zero anchor's
canonical `M0` color condition. -/
theorem perfectMatching_gap02_normalForm
    {L alpha beta z0 z1 z2 z3 : Turn}
    (h02 : TurnSequenceAllowed z0 alpha z2 beta)
    (h12 : TurnSequenceAllowed z1 L z2 beta)
    (hmatching : IsBasePerfectMatching
      ((z0 = alpha) ∧ (z1 = L)) ((z0 = alpha) ∧ (z2 = beta))
      ((z0 = alpha) ∧ (z3 = beta)) ((z1 = L) ∧ (z2 = beta))
      ((z1 = L) ∧ (z3 = beta)) ((z2 = beta) ↔ (z3 = beta))) :
    IsBaseMatching0
        ((z0 = alpha) ∧ (z1 = L)) ((z0 = alpha) ∧ (z2 = beta))
        ((z0 = alpha) ∧ (z3 = beta)) ((z1 = L) ∧ (z2 = beta))
        ((z1 = L) ∧ (z3 = beta)) ((z2 = beta) ↔ (z3 = beta)) ∧
      alpha = L ∧ alpha ≠ beta := by
  have hm := perfectMatching_middleGap_pattern hmatching
  refine ⟨hm, ?_⟩
  rcases hm with ⟨⟨hz0, hz1⟩, _, hn02, _, _, _⟩
  have hz2b : z2 ≠ beta := by
    intro hb
    exact hn02 ⟨hz0, hb⟩
  have haz2 : alpha = z2 :=
    hz0.symm.trans (h02.eq_first_of_first_eq_of_last_ne hz0 hz2b)
  have hLz2 : L = z2 :=
    hz1.symm.trans (h12.eq_first_of_first_eq_of_last_ne hz1 hz2b)
  refine ⟨haz2.trans hLz2.symm, ?_⟩
  intro hab
  exact hz2b (haz2.symm.trans hab)

/-- In placement `12`, the unique matching forces the gap-one anchor's
canonical `M0` color condition. -/
theorem perfectMatching_gap12_normalForm
    {L alpha beta z0 z1 z2 z3 : Turn}
    (h02 : TurnSequenceAllowed z0 alpha beta z2)
    (h12 : TurnSequenceAllowed z1 L z2 beta)
    (hmatching : IsBasePerfectMatching
      ((z0 = alpha) ∧ (z1 = L)) ((z0 = alpha) ∧ (z2 = beta))
      ((z0 = alpha) ∧ (z3 = beta)) ((z1 = L) ∧ (z2 = beta))
      ((z1 = L) ∧ (z3 = beta)) ((z2 = beta) ↔ (z3 = beta))) :
    IsBaseMatching0
        ((z0 = alpha) ∧ (z1 = L)) ((z0 = alpha) ∧ (z2 = beta))
        ((z0 = alpha) ∧ (z3 = beta)) ((z1 = L) ∧ (z2 = beta))
        ((z1 = L) ∧ (z3 = beta)) ((z2 = beta) ↔ (z3 = beta)) ∧
      alpha = beta ∧ alpha ≠ L := by
  have hm := perfectMatching_middleGap_pattern hmatching
  refine ⟨hm, ?_⟩
  rcases hm with ⟨⟨hz0, hz1⟩, _, hn02, _, _, _⟩
  have hz2b : z2 ≠ beta := by
    intro hb
    exact hn02 ⟨hz0, hb⟩
  have hab : alpha = beta :=
    hz0.symm.trans (h02.eq_first_of_first_eq_of_last_ne hz0 (Ne.symm hz2b))
  have hLz2 : L = z2 :=
    hz1.symm.trans (h12.eq_first_of_first_eq_of_last_ne hz1 hz2b)
  refine ⟨hab, ?_⟩
  intro haL
  exact hz2b (hLz2.symm.trans (haL.symm.trans hab))

/-- A perfect matching in the central placement is necessarily `M0`. -/
theorem perfectMatching_sameMiddleGap_pattern
    {P0 P1 Q2 Q3 : Prop}
    (hmatching : IsBasePerfectMatching
      (P0 ↔ P1) (P0 ∧ Q2) (P0 ∧ Q3)
      (P1 ∧ Q2) (P1 ∧ Q3) (Q2 ↔ Q3)) :
    IsBaseMatching0
      (P0 ↔ P1) (P0 ∧ Q2) (P0 ∧ Q3)
      (P1 ∧ Q2) (P1 ∧ Q3) (Q2 ↔ Q3) := by
  rcases hmatching with hm | hm | hm
  · exact hm
  · rcases hm with ⟨⟨hP0, hQ2⟩, ⟨hP1, hQ3⟩, hn01, _, _, _⟩
    exact (hn01 ⟨fun _ ↦ hP1, fun _ ↦ hP0⟩).elim
  · rcases hm with ⟨⟨hP0, hQ3⟩, ⟨hP1, hQ2⟩, hn01, _, _, _⟩
    exact (hn01 ⟨fun _ ↦ hP1, fun _ ↦ hP0⟩).elim

/-- A clique on an active subset of four vertices is never a perfect matching. -/
theorem not_perfectMatching_activeClique {P0 P1 P2 P3 : Prop} :
    ¬IsBasePerfectMatching
      (P0 ∧ P1) (P0 ∧ P2) (P0 ∧ P3)
      (P1 ∧ P2) (P1 ∧ P3) (P2 ∧ P3) := by
  intro hmatching
  rcases hmatching with hm | hm | hm
  · rcases hm with ⟨⟨hP0, hP1⟩, ⟨hP2, hP3⟩, hn02, _, _, _⟩
    exact hn02 ⟨hP0, hP2⟩
  · rcases hm with ⟨⟨hP0, hP2⟩, ⟨hP1, hP3⟩, hn01, _, _, _⟩
    exact hn01 ⟨hP0, hP1⟩
  · rcases hm with ⟨⟨hP0, hP3⟩, ⟨hP1, hP2⟩, hn01, _, _, _⟩
    exact hn01 ⟨hP0, hP1⟩

/-- If a binary status is constant on both edges of a matching and differs
across the two edges, one matching edge has positive status at both ends. -/
theorem exists_positive_matchingEdge_of_status_relations
    {P0 P1 P2 P3 : Prop}
    (h01 : P0 ↔ P1) (h23 : P2 ↔ P3) (h02 : ¬(P0 ↔ P2)) :
    (P0 ∧ P1) ∨ (P2 ∧ P3) := by
  by_cases h0 : P0
  · exact Or.inl ⟨h0, h01.mp h0⟩
  · right
    have h2 : P2 := by
      by_contra hn2
      apply h02
      constructor <;> intro h
      · exact (h0 h).elim
      · exact (hn2 h).elim
    exact ⟨h2, h23.mp h2⟩

/-- The actual cross-edge proposition on a labeled ordered four-base. -/
def StrongCrossEdge {n : ℕ} (χ : TripleColoring n) (e : Fin 4 ↪o Fin n)
    (o p : Fin n) (i j : Fin 4) : Prop :=
  IsStrongPolygonSet χ {o, p, e i, e j}

/-- The six actual cross edges form a perfect matching on the labeled base. -/
def IsPerfectCrossMatching {n : ℕ} (χ : TripleColoring n)
    (e : Fin 4 ↪o Fin n) (o p : Fin n) : Prop :=
  IsBasePerfectMatching
    (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
    (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
    (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3)

/-- A vertex outside an ordered four-base lies in exactly one of its five
sweep gaps; this disjunction is the router for the placement normal forms. -/
theorem outside_orderedFour_gap_cases
    {n : ℕ} (e : Fin 4 ↪o Fin n) {o : Fin n}
    (ho : o ∉ Finset.univ.image e) :
    o < e 0 ∨
      (e 0 < o ∧ o < e 1) ∨
      (e 1 < o ∧ o < e 2) ∨
      (e 2 < o ∧ o < e 3) ∨
      e 3 < o := by
  have hne : ∀ i : Fin 4, o ≠ e i := by
    intro i hoi
    apply ho
    rw [hoi]
    simp
  rcases lt_or_gt_of_ne (hne 0) with h0 | h0
  · exact Or.inl h0
  rcases lt_or_gt_of_ne (hne 1) with h1 | h1
  · exact Or.inr (Or.inl ⟨h0, h1⟩)
  rcases lt_or_gt_of_ne (hne 2) with h2 | h2
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))
  rcases lt_or_gt_of_ne (hne 3) with h3 | h3
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h3⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))

/-- Actual order transport for the representative in which both owners lie
to the right of the ordered four-base. -/
theorem perfectCrossMatching_sameRight_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h3o : e 3 < o) (hop : o < p)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let L := χ ⟨e 0, e 1, e 2, e.strictMono (by omega), e.strictMono (by omega)⟩
    let R := χ ⟨e 0, e 2, e 3, e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨e 2, e 3, o, e.strictMono (by omega), h3o⟩
    let beta := χ ⟨e 2, e 3, p, e.strictMono (by omega), h3o.trans hop⟩
    (IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = R) ∨
    (IsBaseMatching1
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = L ∧ L ≠ R) ∨
    (IsBaseMatching2
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ L = R ∧ L ≠ alpha) := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h03 : e 0 < e 3 := h02.trans h23
  have h13 : e 1 < e 3 := h12.trans h23
  have h0o : e 0 < o := h03.trans h3o
  have h1o : e 1 < o := h13.trans h3o
  have h2o : e 2 < o := h23.trans h3o
  have h0p : e 0 < p := h0o.trans hop
  have h1p : e 1 < p := h1o.trans hop
  have h2p : e 2 < p := h2o.trans hop
  have h3p : e 3 < p := h3o.trans hop
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 2, e 3, o, h23, h3o⟩
  let beta : Turn := χ ⟨e 2, e 3, p, h23, h3p⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨e 1, o, p, h1o, hop⟩
  let z2 : Turn := χ ⟨e 2, o, p, h2o, hop⟩
  let z3 : Turn := χ ⟨e 3, o, p, h3o, hop⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho01 : χ ⟨e 0, e 1, o, h01, h1o⟩ = L := by
    simpa [L] using hmo h01 h01 h1o h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho02 : χ ⟨e 0, e 2, o, h02, h2o⟩ = R := by
    simpa [R] using hmo h02 h02 h2o h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, e 2, p, h02, h2p⟩ = R := by
    simpa [R] using hmp h02 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho12 : χ ⟨e 1, e 2, o, h12, h2o⟩ = R := by
    simpa [R] using hmo h12 h02 h2o h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨e 1, e 2, p, h12, h2p⟩ = R := by
    simpa [R] using hmp h12 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨e 0, e 3, o, h03, h3o⟩ = alpha := by
    simpa [alpha] using hmo h03 h23 h3o h3o (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, e 3, p, h03, h3p⟩ = beta := by
    simpa [beta] using hmp h03 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨e 1, e 3, o, h13, h3o⟩ = alpha := by
    simpa [alpha] using hmo h13 h23 h3o h3o (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, e 3, p, h13, h3p⟩ = beta := by
    simpa [beta] using hmp h13 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨e 2, e 3, o, h23, h3o⟩ = alpha := by rfl
  have hp23 : χ ⟨e 2, e 3, p, h23, h3p⟩ = beta := by rfl
  have ha01 : TurnSequenceAllowed L L z0 z1 := by
    simpa [L, z0, z1, ho01, hp01] using
      hone h01 h1o hop (by simp) (by simp) (by simp) (by simp)
  have ha02 : TurnSequenceAllowed R R z0 z2 := by
    simpa [R, z0, z2, ho02, hp02] using
      hone h02 h2o hop (by simp) (by simp) (by simp) (by simp)
  have ha12 : TurnSequenceAllowed R R z1 z2 := by
    simpa [R, z1, z2, ho12, hp12] using
      hone h12 h2o hop (by simp) (by simp) (by simp) (by simp)
  have ha03 : TurnSequenceAllowed alpha beta z0 z3 := by
    simpa [alpha, beta, z0, z3, ho03, hp03] using
      hone h03 h3o hop (by simp) (by simp) (by simp) (by simp)
  have ha13 : TurnSequenceAllowed alpha beta z1 z3 := by
    simpa [alpha, beta, z1, z3, ho13, hp13] using
      hone h13 h3o hop (by simp) (by simp) (by simp) (by simp)
  have ha23 : TurnSequenceAllowed alpha beta z2 z3 := by
    simpa [alpha, beta, z2, z3, ho23, hp23] using
      hone h23 h3o hop (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = z1 := by
    change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ z0 = z1
    rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {e 0, e 1, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    simpa [StrongCrossEdge, z0, z1, ho01, hp01] using
      (isStrongPolygonSet_four_iff (χ := χ) h01 h1o hop)
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = z2 := by
    change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ z0 = z2
    rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {e 0, e 2, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    simpa [z0, z2, ho02, hp02] using
      (isStrongPolygonSet_four_iff (χ := χ) h02 h2o hop)
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = z2 := by
    change IsStrongPolygonSet χ {o, p, e 1, e 2} ↔ z1 = z2
    rw [show ({o, p, e 1, e 2} : Finset (Fin n)) = {e 1, e 2, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    simpa [z1, z2, ho12, hp12] using
      (isStrongPolygonSet_four_iff (χ := χ) h12 h2o hop)
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ alpha = beta ∧ z0 = z3 := by
    change IsStrongPolygonSet χ {o, p, e 0, e 3} ↔ alpha = beta ∧ z0 = z3
    rw [show ({o, p, e 0, e 3} : Finset (Fin n)) = {e 0, e 3, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    simpa [alpha, beta, z0, z3, ho03, hp03] using
      (isStrongPolygonSet_four_iff (χ := χ) h03 h3o hop)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ alpha = beta ∧ z1 = z3 := by
    change IsStrongPolygonSet χ {o, p, e 1, e 3} ↔ alpha = beta ∧ z1 = z3
    rw [show ({o, p, e 1, e 3} : Finset (Fin n)) = {e 1, e 3, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    simpa [alpha, beta, z1, z3, ho13, hp13] using
      (isStrongPolygonSet_four_iff (χ := χ) h13 h3o hop)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ alpha = beta ∧ z2 = z3 := by
    change IsStrongPolygonSet χ {o, p, e 2, e 3} ↔ alpha = beta ∧ z2 = z3
    rw [show ({o, p, e 2, e 3} : Finset (Fin n)) = {e 2, e 3, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    simpa [alpha, beta, z2, z3, ho23, hp23] using
      (isStrongPolygonSet_four_iff (χ := χ) h23 h3o hop)
  have hpure : IsBasePerfectMatching
      (z0 = z1) (z0 = z2) (alpha = beta ∧ z0 = z3)
      (z1 = z2) (alpha = beta ∧ z1 = z3)
      (alpha = beta ∧ z2 = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hnormal := perfectMatching_sameRight_normalForm
    ha01 ha02 ha12 ha03 ha13 ha23 hpure
  simpa [L, R, alpha, beta, IsBaseMatching0, IsBaseMatching1,
    IsBaseMatching2, he01, he02, he03, he12, he13, he23] using hnormal

/-- Actual order transport for the missing order-dual representative in which
both owners lie to the left of the ordered four-base. -/
theorem perfectCrossMatching_sameLeft_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (hop : o < p) (hp0 : p < e 0)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let L := χ ⟨e 0, e 1, e 2, e.strictMono (by omega), e.strictMono (by omega)⟩
    let R := χ ⟨e 0, e 2, e 3, e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨o, e 0, e 1, hop.trans hp0, e.strictMono (by omega)⟩
    let beta := χ ⟨p, e 0, e 1, hp0, e.strictMono (by omega)⟩
    (IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = L) ∨
    (IsBaseMatching1
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = R ∧ R ≠ L) ∨
    (IsBaseMatching2
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ L = R ∧ L ≠ alpha) := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h03 : e 0 < e 3 := h02.trans h23
  have ho0 : o < e 0 := hop.trans hp0
  have ho1 : o < e 1 := ho0.trans h01
  have ho2 : o < e 2 := ho0.trans h02
  have ho3 : o < e 3 := ho0.trans h03
  have hp1 : p < e 1 := hp0.trans h01
  have hp2 : p < e 2 := hp0.trans h02
  have hp3 : p < e 3 := hp0.trans h03
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨o, e 0, e 1, ho0, h01⟩
  let beta : Turn := χ ⟨p, e 0, e 1, hp0, h01⟩
  let z0 : Turn := χ ⟨o, p, e 0, hop, hp0⟩
  let z1 : Turn := χ ⟨o, p, e 1, hop, hp1⟩
  let z2 : Turn := χ ⟨o, p, e 2, hop, hp2⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨o, e 0, e 2, ho0, h02⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 h02 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨p, e 0, e 2, hp0, h02⟩ = beta := by
    simpa [beta] using hmp hp0 hp0 h02 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨o, e 0, e 3, ho0, h03⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 h03 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨p, e 0, e 3, hp0, h03⟩ = beta := by
    simpa [beta] using hmp hp0 hp0 h03 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨p, e 1, e 2, hp1, h12⟩ = L := by
    simpa [L] using hmp hp1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h12.trans h23⟩ = L := by
    simpa [L] using hmo ho1 h01 (h12.trans h23) h12 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have hp13 : χ ⟨p, e 1, e 3, hp1, h12.trans h23⟩ = L := by
    simpa [L] using hmp hp1 h01 (h12.trans h23) h12 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp23 : χ ⟨p, e 2, e 3, hp2, h23⟩ = R := by
    simpa [R] using hmp hp2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ha01 : TurnSequenceAllowed z0 z1 alpha beta := by
    simpa [z0, z1, alpha, beta] using
      hone hop hp0 h01 (by simp) (by simp) (by simp) (by simp)
  have ha02 : TurnSequenceAllowed z0 z2 alpha beta := by
    simpa [z0, z2, alpha, beta, ho02, hp02] using
      hone hop hp0 h02 (by simp) (by simp) (by simp) (by simp)
  have ha03 : TurnSequenceAllowed z0 z3 alpha beta := by
    simpa [z0, z3, alpha, beta, ho03, hp03] using
      hone hop hp0 h03 (by simp) (by simp) (by simp) (by simp)
  have ha12 : TurnSequenceAllowed z1 z2 L L := by
    simpa [z1, z2, L, ho12, hp12] using
      hone hop hp1 h12 (by simp) (by simp) (by simp) (by simp)
  have ha13 : TurnSequenceAllowed z1 z3 L L := by
    simpa [z1, z3, L, ho13, hp13] using
      hone hop hp1 (h12.trans h23) (by simp) (by simp) (by simp) (by simp)
  have ha23 : TurnSequenceAllowed z2 z3 R R := by
    simpa [z2, z3, R, ho23, hp23] using
      hone hop hp2 h23 (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ alpha = beta ∧ z0 = z1 := by
    have hraw : StrongCrossEdge χ e o p 0 1 ↔ z0 = z1 ∧ alpha = beta := by
      simpa [StrongCrossEdge, z0, z1, alpha, beta] using
        (isStrongPolygonSet_four_iff (χ := χ) hop hp0 h01)
    exact hraw.trans ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ alpha = beta ∧ z0 = z2 := by
    have hraw : StrongCrossEdge χ e o p 0 2 ↔ z0 = z2 ∧ alpha = beta := by
      simpa [StrongCrossEdge, z0, z2, alpha, beta, ho02, hp02] using
        (isStrongPolygonSet_four_iff (χ := χ) hop hp0 h02)
    exact hraw.trans ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ alpha = beta ∧ z0 = z3 := by
    have hraw : StrongCrossEdge χ e o p 0 3 ↔ z0 = z3 ∧ alpha = beta := by
      simpa [StrongCrossEdge, z0, z3, alpha, beta, ho03, hp03] using
        (isStrongPolygonSet_four_iff (χ := χ) hop hp0 h03)
    exact hraw.trans ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = z2 := by
    simpa [StrongCrossEdge, z1, z2, L, ho12, hp12] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp1 h12)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = z3 := by
    simpa [StrongCrossEdge, z1, z3, L, ho13, hp13] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp1 (h12.trans h23))
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = z3 := by
    simpa [StrongCrossEdge, z2, z3, R, ho23, hp23] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp2 h23)
  have hpure : IsBasePerfectMatching
      (alpha = beta ∧ z0 = z1) (alpha = beta ∧ z0 = z2)
      (alpha = beta ∧ z0 = z3) (z1 = z2) (z1 = z3) (z2 = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hnormal := perfectMatching_sameLeft_normalForm
    ha01 ha02 ha03 ha12 ha13 ha23 hpure
  simpa [L, R, alpha, beta, IsBaseMatching0, IsBaseMatching1,
    IsBaseMatching2, he01, he02, he03, he12, he13, he23] using hnormal

/-- Actual order transport when both owners lie in the first internal base
gap. -/
theorem perfectCrossMatching_sameFirstGap_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h0o : e 0 < o) (hop : o < p) (hp1 : p < e 1)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let L := χ ⟨e 0, e 1, e 2, e.strictMono (by omega), e.strictMono (by omega)⟩
    let R := χ ⟨e 0, e 2, e 3, e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨e 0, o, e 1, h0o, hop.trans hp1⟩
    let beta := χ ⟨e 0, p, e 1, h0o.trans hop, hp1⟩
    (IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha ≠ L) ∨
    (IsBaseMatching1
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = L ∧ L ≠ R) ∨
    (IsBaseMatching2
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = L ∧ L = R) := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h13 : e 1 < e 3 := h12.trans h23
  have ho1 : o < e 1 := hop.trans hp1
  have h0p : e 0 < p := h0o.trans hop
  have ho2 : o < e 2 := ho1.trans h12
  have hp2 : p < e 2 := hp1.trans h12
  have ho3 : o < e 3 := ho2.trans h23
  have hp3 : p < e 3 := hp2.trans h23
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 0, o, e 1, h0o, ho1⟩
  let beta : Turn := χ ⟨e 0, p, e 1, h0p, hp1⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨o, p, e 1, hop, hp1⟩
  let z2 : Turn := χ ⟨o, p, e 2, hop, hp2⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨e 0, o, e 2, h0o, ho2⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho2 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have hp02 : χ ⟨e 0, p, e 2, h0p, hp2⟩ = beta := by
    simpa [beta] using
      hmp h0p h0p hp2 hp1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho03 : χ ⟨e 0, o, e 3, h0o, ho3⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho3 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using
      hmp h0p h0p hp3 hp1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨p, e 1, e 2, hp1, h12⟩ = L := by
    simpa [L] using hmp hp1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h13⟩ = L := by
    simpa [L] using hmo ho1 h01 h13 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨p, e 1, e 3, hp1, h13⟩ = L := by
    simpa [L] using hmp hp1 h01 h13 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp23 : χ ⟨p, e 2, e 3, hp2, h23⟩ = R := by
    simpa [R] using hmp hp2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ha01 : TurnSequenceAllowed z0 alpha beta z1 := by
    simpa [z0, alpha, beta, z1] using
      hone h0o hop hp1 (by simp) (by simp) (by simp) (by simp)
  have ha02 : TurnSequenceAllowed z0 alpha beta z2 := by
    simpa [z0, alpha, beta, z2, ho02, hp02] using
      hone h0o hop hp2 (by simp) (by simp) (by simp) (by simp)
  have ha03 : TurnSequenceAllowed z0 alpha beta z3 := by
    simpa [z0, alpha, beta, z3, ho03, hp03] using
      hone h0o hop hp3 (by simp) (by simp) (by simp) (by simp)
  have ha12 : TurnSequenceAllowed z1 z2 L L := by
    simpa [z1, z2, L, ho12, hp12] using
      hone hop hp1 h12 (by simp) (by simp) (by simp) (by simp)
  have ha13 : TurnSequenceAllowed z1 z3 L L := by
    simpa [z1, z3, L, ho13, hp13] using
      hone hop hp1 h13 (by simp) (by simp) (by simp) (by simp)
  have ha23 : TurnSequenceAllowed z2 z3 R R := by
    simpa [z2, z3, R, ho23, hp23] using
      hone hop hp2 h23 (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ beta = z1 := by
    simpa [StrongCrossEdge, z0, alpha, beta, z1, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp1)
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ beta = z2 := by
    simpa [StrongCrossEdge, z0, alpha, beta, z2, ho02, hp02,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp2)
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ beta = z3 := by
    simpa [StrongCrossEdge, z0, alpha, beta, z3, ho03, hp03,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp3)
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = z2 := by
    simpa [StrongCrossEdge, z1, z2, ho12, hp12, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp1 h12)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = z3 := by
    simpa [StrongCrossEdge, z1, z3, ho13, hp13, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp1 h13)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = z3 := by
    simpa [StrongCrossEdge, z2, z3, ho23, hp23, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp2 h23)
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ beta = z1) (z0 = alpha ∧ beta = z2)
      (z0 = alpha ∧ beta = z3) (z1 = z2) (z1 = z3) (z2 = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hnormal := perfectMatching_sameFirstGap_normalForm
    ha01 ha02 ha03 ha12 ha13 ha23 hpure
  simpa [L, R, alpha, beta, IsBaseMatching0, IsBaseMatching1,
    IsBaseMatching2, he01, he02, he03, he12, he13, he23] using hnormal

/-- Equality-edge specialization of the central-gap graph pattern. -/
theorem perfectMatching_sameMiddleGap_eq_pattern
    {alpha beta z0 z1 z2 z3 : Turn}
    (hmatching : IsBasePerfectMatching
      (z0 = z1) (z0 = alpha ∧ beta = z2) (z0 = alpha ∧ beta = z3)
      (z1 = alpha ∧ beta = z2) (z1 = alpha ∧ beta = z3) (z2 = z3)) :
    IsBaseMatching0
      (z0 = z1) (z0 = alpha ∧ beta = z2) (z0 = alpha ∧ beta = z3)
      (z1 = alpha ∧ beta = z2) (z1 = alpha ∧ beta = z3) (z2 = z3) := by
  rcases hmatching with hm | hm | hm
  · exact hm
  · rcases hm with ⟨⟨hz0, _⟩, ⟨hz1, _⟩, hn01, _, _, _⟩
    exact (hn01 (hz0.trans hz1.symm)).elim
  · rcases hm with ⟨⟨hz0, _⟩, ⟨hz1, _⟩, hn01, _, _, _⟩
    exact (hn01 (hz0.trans hz1.symm)).elim

/-- Actual order transport when both owners lie in the middle base gap. -/
theorem perfectCrossMatching_sameMiddleGap_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h1o : e 1 < o) (hop : o < p) (hp2 : p < e 2)
    (_hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    IsBaseMatching0
      (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
      (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
      (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) := by
  classical
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h0o : e 0 < o := h01.trans h1o
  have h1p : e 1 < p := h1o.trans hop
  have ho2 : o < e 2 := hop.trans hp2
  have h0p : e 0 < p := h01.trans h1p
  have ho3 : o < e 3 := ho2.trans h23
  have hp3 : p < e 3 := hp2.trans h23
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 1, o, e 2, h1o, ho2⟩
  let beta : Turn := χ ⟨e 1, p, e 2, h1p, hp2⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨e 1, o, p, h1o, hop⟩
  let z2 : Turn := χ ⟨o, p, e 2, hop, hp2⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho01 : χ ⟨e 0, e 1, o, h01, h1o⟩ = L := by
    simpa [L] using hmo h01 h01 h1o h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho02 : χ ⟨e 0, o, e 2, h0o, ho2⟩ = alpha := by
    simpa [alpha] using hmo h0o h1o ho2 ho2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, p, e 2, h0p, hp2⟩ = beta := by
    simpa [beta] using hmp h0p h1p hp2 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨e 0, o, e 3, h0o, ho3⟩ = alpha := by
    simpa [alpha] using hmo h0o h1o ho3 ho2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using hmp h0p h1p hp3 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨e 1, o, e 3, h1o, ho3⟩ = alpha := by
    simpa [alpha] using hmo h1o h1o ho3 ho2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, p, e 3, h1p, hp3⟩ = beta := by
    simpa [beta] using hmp h1p h1p hp3 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp23 : χ ⟨p, e 2, e 3, hp2, h23⟩ = R := by
    simpa [R] using hmp hp2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = z1 := by
    change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ z0 = z1
    rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {e 0, e 1, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    simpa [z0, z1, L, ho01, hp01] using
      (isStrongPolygonSet_four_iff (χ := χ) h01 h1o hop)
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ beta = z2 := by
    simpa [StrongCrossEdge, z0, alpha, beta, z2, ho02, hp02,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp2)
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ beta = z3 := by
    simpa [StrongCrossEdge, z0, alpha, beta, z3, ho03, hp03,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp3)
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = alpha ∧ beta = z2 := by
    simpa [StrongCrossEdge, z1, alpha, beta, z2, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h1o hop hp2)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = alpha ∧ beta = z3 := by
    simpa [StrongCrossEdge, z1, alpha, beta, z3, ho13, hp13,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h1o hop hp3)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = z3 := by
    simpa [StrongCrossEdge, z2, z3, R, ho23, hp23, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp2 h23)
  have hpure : IsBasePerfectMatching
      (z0 = z1) (z0 = alpha ∧ beta = z2) (z0 = alpha ∧ beta = z3)
      (z1 = alpha ∧ beta = z2) (z1 = alpha ∧ beta = z3) (z2 = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hnormal := perfectMatching_sameMiddleGap_eq_pattern hpure
  simpa [IsBaseMatching0, he01, he02, he03, he12, he13, he23] using hnormal

/-- Actual order transport for owners in the two consecutive left sweep gaps. -/
theorem perfectCrossMatching_leftAdjacent_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (ho0 : o < e 0) (h0p : e 0 < p) (hp1 : p < e 1)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let L := χ ⟨e 0, e 1, e 2, e.strictMono (by omega), e.strictMono (by omega)⟩
    let R := χ ⟨e 0, e 2, e 3, e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨o, e 0, e 1, ho0, e.strictMono (by omega)⟩
    let beta := χ ⟨e 0, p, e 1, h0p, hp1⟩
    (IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = L ∧ beta ≠ L) ∨
    (IsBaseMatching1
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = R ∧ R ≠ L ∧ beta = L) ∨
    (IsBaseMatching2
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      L = R ∧ beta = L ∧ alpha ≠ L) := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have hop : o < p := ho0.trans h0p
  have ho1 : o < e 1 := ho0.trans h01
  have ho2 : o < e 2 := ho1.trans h12
  have hp2 : p < e 2 := hp1.trans h12
  have ho3 : o < e 3 := ho2.trans h23
  have hp3 : p < e 3 := hp2.trans h23
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨o, e 0, e 1, ho0, h01⟩
  let beta : Turn := χ ⟨e 0, p, e 1, h0p, hp1⟩
  let z0 : Turn := χ ⟨o, e 0, p, ho0, h0p⟩
  let z1 : Turn := χ ⟨o, p, e 1, hop, hp1⟩
  let z2 : Turn := χ ⟨o, p, e 2, hop, hp2⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨o, e 0, e 2, ho0, h02⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 h02 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, p, e 2, h0p, hp2⟩ = beta := by
    simpa [beta] using
      hmp h0p h0p hp2 hp1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho03 : χ ⟨o, e 0, e 3, ho0, h02.trans h23⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 (h02.trans h23) h01 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using
      hmp h0p h0p hp3 hp1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨p, e 1, e 2, hp1, h12⟩ = L := by
    simpa [L] using hmp hp1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h12.trans h23⟩ = L := by
    simpa [L] using hmo ho1 h01 (h12.trans h23) h12 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have hp13 : χ ⟨p, e 1, e 3, hp1, h12.trans h23⟩ = L := by
    simpa [L] using hmp hp1 h01 (h12.trans h23) h12 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp23 : χ ⟨p, e 2, e 3, hp2, h23⟩ = R := by
    simpa [R] using hmp hp2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ha01 : TurnSequenceAllowed z0 alpha z1 beta := by
    simpa [z0, alpha, z1, beta] using
      hone ho0 h0p hp1 (by simp) (by simp) (by simp) (by simp)
  have ha02 : TurnSequenceAllowed z0 alpha z2 beta := by
    simpa [z0, alpha, z2, beta, ho02, hp02] using
      hone ho0 h0p hp2 (by simp) (by simp) (by simp) (by simp)
  have ha03 : TurnSequenceAllowed z0 alpha z3 beta := by
    simpa [z0, alpha, z3, beta, ho03, hp03] using
      hone ho0 h0p hp3 (by simp) (by simp) (by simp) (by simp)
  have ha12 : TurnSequenceAllowed z1 z2 L L := by
    simpa [z1, z2, L, ho12, hp12] using
      hone hop hp1 h12 (by simp) (by simp) (by simp) (by simp)
  have ha13 : TurnSequenceAllowed z1 z3 L L := by
    simpa [z1, z3, L, ho13, hp13] using
      hone hop hp1 (h12.trans h23) (by simp) (by simp) (by simp) (by simp)
  have ha23 : TurnSequenceAllowed z2 z3 R R := by
    simpa [z2, z3, R, ho23, hp23] using
      hone hop hp2 h23 (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ z1 = beta := by
    simpa [StrongCrossEdge, z0, alpha, z1, beta, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho0 h0p hp1)
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = beta := by
    simpa [StrongCrossEdge, z0, alpha, z2, beta, ho02, hp02,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho0 h0p hp2)
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    simpa [StrongCrossEdge, z0, alpha, z3, beta, ho03, hp03,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho0 h0p hp3)
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = z2 := by
    simpa [StrongCrossEdge, z1, z2, L, ho12, hp12, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp1 h12)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = z3 := by
    simpa [StrongCrossEdge, z1, z3, L, ho13, hp13, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp1 (h12.trans h23))
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = z3 := by
    simpa [StrongCrossEdge, z2, z3, R, ho23, hp23, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp2 h23)
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = beta) (z0 = alpha ∧ z2 = beta)
      (z0 = alpha ∧ z3 = beta) (z1 = z2) (z1 = z3) (z2 = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hnormal := perfectMatching_leftAdjacent_normalForm
    ha01 ha02 ha03 ha12 ha13 ha23 hpure
  simpa [L, R, alpha, beta, IsBaseMatching0, IsBaseMatching1,
    IsBaseMatching2, he01, he02, he03, he12, he13, he23] using hnormal

/-- Equality-tail specialization of the middle-gap graph pattern. -/
theorem perfectMatching_middleGap_eqTail_pattern
    {P Q : Prop} {beta z2 z3 : Turn}
    (hmatching : IsBasePerfectMatching
      (P ∧ Q) (P ∧ z2 = beta) (P ∧ z3 = beta)
      (Q ∧ z2 = beta) (Q ∧ z3 = beta) (z2 = z3)) :
    IsBaseMatching0
      (P ∧ Q) (P ∧ z2 = beta) (P ∧ z3 = beta)
      (Q ∧ z2 = beta) (Q ∧ z3 = beta) (z2 = z3) := by
  rcases hmatching with hm | hm | hm
  · exact hm
  · rcases hm with ⟨⟨_, hz2⟩, ⟨_, hz3⟩, _, _, _, hn23⟩
    exact (hn23 (hz2.trans hz3.symm)).elim
  · rcases hm with ⟨⟨_, hz3⟩, ⟨_, hz2⟩, _, _, _, hn23⟩
    exact (hn23 (hz2.trans hz3.symm)).elim

/-- Actual order transport for a gap-zero owner followed by a middle-gap
owner. -/
theorem perfectCrossMatching_gap02_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (ho0 : o < e 0) (h1p : e 1 < p) (hp2 : p < e 2)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let L := χ ⟨e 0, e 1, e 2, e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨o, e 0, e 1, ho0, e.strictMono (by omega)⟩
    let beta := χ ⟨e 1, p, e 2, h1p, hp2⟩
    IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = L ∧ alpha ≠ beta := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h0p : e 0 < p := h01.trans h1p
  have hop : o < p := ho0.trans h0p
  have ho1 : o < e 1 := ho0.trans h01
  have ho2 : o < e 2 := ho1.trans h12
  have ho3 : o < e 3 := ho2.trans h23
  have hp3 : p < e 3 := hp2.trans h23
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨o, e 0, e 1, ho0, h01⟩
  let beta : Turn := χ ⟨e 1, p, e 2, h1p, hp2⟩
  let z0 : Turn := χ ⟨o, e 0, p, ho0, h0p⟩
  let z1 : Turn := χ ⟨o, e 1, p, ho1, h1p⟩
  let z2 : Turn := χ ⟨o, p, e 2, hop, hp2⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨o, e 0, e 2, ho0, h02⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 h02 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, p, e 2, h0p, hp2⟩ = beta := by
    simpa [beta] using hmp h0p h1p hp2 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨o, e 0, e 3, ho0, h02.trans h23⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 (h02.trans h23) h01 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using hmp h0p h1p hp3 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h12.trans h23⟩ = L := by
    simpa [L] using hmo ho1 h01 (h12.trans h23) h12 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have hp13 : χ ⟨e 1, p, e 3, h1p, hp3⟩ = beta := by
    simpa [beta] using hmp h1p h1p hp3 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp23 : χ ⟨p, e 2, e 3, hp2, h23⟩ = R := by
    simpa [R] using hmp hp2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ha02 : TurnSequenceAllowed z0 alpha z2 beta := by
    simpa [z0, alpha, z2, beta, ho02, hp02] using
      hone ho0 h0p hp2 (by simp) (by simp) (by simp) (by simp)
  have ha12 : TurnSequenceAllowed z1 L z2 beta := by
    simpa [z1, L, z2, beta, ho12] using
      hone ho1 h1p hp2 (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ z1 = L := by
    have hraw : StrongCrossEdge χ e o p 0 1 ↔ alpha = z0 ∧ z1 = L := by
      change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ alpha = z0 ∧ z1 = L
      rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {o, e 0, e 1, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
      simpa [alpha, z0, z1, L, hp01] using
        (isStrongPolygonSet_four_iff (χ := χ) ho0 h01 h1p)
    exact hraw.trans ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = beta := by
    simpa [StrongCrossEdge, z0, alpha, z2, beta, ho02, hp02,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho0 h0p hp2)
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    simpa [StrongCrossEdge, z0, alpha, z3, beta, ho03, hp03,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho0 h0p hp3)
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = L ∧ z2 = beta := by
    simpa [StrongCrossEdge, z1, L, z2, beta, ho12, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho1 h1p hp2)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = L ∧ z3 = beta := by
    simpa [StrongCrossEdge, z1, L, z3, beta, ho13, hp13,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho1 h1p hp3)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = z3 := by
    simpa [StrongCrossEdge, z2, z3, R, ho23, hp23, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp2 h23)
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = beta)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = beta)
      (z1 = L ∧ z3 = beta) (z2 = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hm := perfectMatching_middleGap_eqTail_pattern hpure
  have hcolors : alpha = L ∧ alpha ≠ beta := by
    rcases hm with ⟨⟨hz0, hz1⟩, _, hn02, _, _, _⟩
    have hz2b : z2 ≠ beta := by
      intro hz2
      exact hn02 ⟨hz0, hz2⟩
    have hz02 : z0 = z2 := ha02.eq_first_of_first_eq_of_last_ne hz0 hz2b
    have hz12 : z1 = z2 := ha12.eq_first_of_first_eq_of_last_ne hz1 hz2b
    refine ⟨hz0.symm.trans (hz02.trans (hz12.symm.trans hz1)), ?_⟩
    intro hab
    exact hz2b (hz02.symm.trans (hz0.trans hab))
  have hnormal : IsBaseMatching0
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = beta)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = beta)
      (z1 = L ∧ z3 = beta) (z2 = z3) ∧ alpha = L ∧ alpha ≠ beta :=
    ⟨hm, hcolors⟩
  simpa [L, alpha, beta, IsBaseMatching0, he01, he02, he03, he12, he13,
    he23] using hnormal

/-- Actual order transport for a gap-one owner followed by a middle-gap
owner. -/
theorem perfectCrossMatching_gap12_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h0o : e 0 < o) (ho1 : o < e 1) (h1p : e 1 < p) (hp2 : p < e 2)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let L := χ ⟨e 0, e 1, e 2, e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨e 0, o, e 1, h0o, ho1⟩
    let beta := χ ⟨e 1, p, e 2, h1p, hp2⟩
    IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha ≠ L := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have hop : o < p := ho1.trans h1p
  have h0p : e 0 < p := h01.trans h1p
  have ho2 : o < e 2 := ho1.trans h12
  have ho3 : o < e 3 := ho2.trans h23
  have hp3 : p < e 3 := hp2.trans h23
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 0, o, e 1, h0o, ho1⟩
  let beta : Turn := χ ⟨e 1, p, e 2, h1p, hp2⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨o, e 1, p, ho1, h1p⟩
  let z2 : Turn := χ ⟨o, p, e 2, hop, hp2⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨e 0, o, e 2, h0o, ho2⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho2 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, p, e 2, h0p, hp2⟩ = beta := by
    simpa [beta] using hmp h0p h1p hp2 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨e 0, o, e 3, h0o, ho3⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho3 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using hmp h0p h1p hp3 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h12.trans h23⟩ = L := by
    simpa [L] using hmo ho1 h01 (h12.trans h23) h12 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have hp13 : χ ⟨e 1, p, e 3, h1p, hp3⟩ = beta := by
    simpa [beta] using hmp h1p h1p hp3 hp2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp23 : χ ⟨p, e 2, e 3, hp2, h23⟩ = R := by
    simpa [R] using hmp hp2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ha02 : TurnSequenceAllowed z0 alpha beta z2 := by
    simpa [z0, alpha, beta, z2, ho02, hp02] using
      hone h0o hop hp2 (by simp) (by simp) (by simp) (by simp)
  have ha12 : TurnSequenceAllowed z1 L z2 beta := by
    simpa [z1, L, z2, beta, ho12] using
      hone ho1 h1p hp2 (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ z1 = L := by
    have hraw : StrongCrossEdge χ e o p 0 1 ↔ alpha = z0 ∧ L = z1 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ alpha = z0 ∧ L = z1
      rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {e 0, o, e 1, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
      simpa [alpha, z0, L, z1, hp01] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho1 h1p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = beta := by
    change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ z0 = alpha ∧ z2 = beta
    rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {e 0, o, p, e 2} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    have hraw : IsStrongPolygonSet χ {e 0, o, p, e 2} ↔
        z0 = alpha ∧ beta = z2 := by
      simpa [z0, alpha, z2, beta, ho02, hp02] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp2)
    exact hraw.trans ⟨fun h ↦ ⟨h.1, h.2.symm⟩, fun h ↦ ⟨h.1, h.2.symm⟩⟩
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    change IsStrongPolygonSet χ {o, p, e 0, e 3} ↔ z0 = alpha ∧ z3 = beta
    rw [show ({o, p, e 0, e 3} : Finset (Fin n)) = {e 0, o, p, e 3} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc]]
    have hraw : IsStrongPolygonSet χ {e 0, o, p, e 3} ↔
        z0 = alpha ∧ beta = z3 := by
      simpa [z0, alpha, z3, beta, ho03, hp03] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp3)
    exact hraw.trans ⟨fun h ↦ ⟨h.1, h.2.symm⟩, fun h ↦ ⟨h.1, h.2.symm⟩⟩
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = L ∧ z2 = beta := by
    simpa [StrongCrossEdge, z1, L, z2, beta, ho12, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho1 h1p hp2)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = L ∧ z3 = beta := by
    simpa [StrongCrossEdge, z1, L, z3, beta, ho13, hp13,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho1 h1p hp3)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = z3 := by
    simpa [StrongCrossEdge, z2, z3, R, ho23, hp23, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) hop hp2 h23)
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = beta)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = beta)
      (z1 = L ∧ z3 = beta) (z2 = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hm := perfectMatching_middleGap_eqTail_pattern hpure
  have hcolors : alpha = beta ∧ alpha ≠ L := by
    rcases hm with ⟨⟨hz0, hz1⟩, _, hn02, _, _, _⟩
    have hz2b : z2 ≠ beta := by
      intro hz2
      exact hn02 ⟨hz0, hz2⟩
    have hz0b : z0 = beta :=
      ha02.eq_first_of_first_eq_of_last_ne hz0 (Ne.symm hz2b)
    have hab : alpha = beta := hz0.symm.trans hz0b
    have hz12 : z1 = z2 := ha12.eq_first_of_first_eq_of_last_ne hz1 hz2b
    refine ⟨hab, ?_⟩
    intro haL
    exact hz2b (hz12.symm.trans (hz1.trans (haL.symm.trans hab)))
  have hnormal : IsBaseMatching0
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = beta)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = beta)
      (z1 = L ∧ z3 = beta) (z2 = z3) ∧ alpha = beta ∧ alpha ≠ L :=
    ⟨hm, hcolors⟩
  simpa [L, alpha, beta, IsBaseMatching0, he01, he02, he03, he12, he13,
    he23] using hnormal

/-- Order-dual normal form when both owners lie in the last internal base gap.
This reverses the six literal one-change words without reversing the ambient
order embedding. -/
theorem perfectMatching_sameLastGap_normalForm
    {L R alpha beta z0 z1 z2 z3 : Turn}
    (h01 : TurnSequenceAllowed L L z0 z1)
    (h02 : TurnSequenceAllowed R R z0 z2)
    (h03 : TurnSequenceAllowed z0 alpha beta z3)
    (h12 : TurnSequenceAllowed R R z1 z2)
    (h13 : TurnSequenceAllowed z1 alpha beta z3)
    (h23 : TurnSequenceAllowed z2 alpha beta z3)
    (hmatching : IsBasePerfectMatching
      (z0 = z1) (z0 = z2) (z0 = alpha ∧ beta = z3)
      (z1 = z2) (z1 = alpha ∧ beta = z3) (z2 = alpha ∧ beta = z3)) :
    (IsBaseMatching0
        (z0 = z1) (z0 = z2) (z0 = alpha ∧ beta = z3)
        (z1 = z2) (z1 = alpha ∧ beta = z3) (z2 = alpha ∧ beta = z3) ∧
      alpha = beta ∧ alpha ≠ R) ∨
    (IsBaseMatching1
        (z0 = z1) (z0 = z2) (z0 = alpha ∧ beta = z3)
        (z1 = z2) (z1 = alpha ∧ beta = z3) (z2 = alpha ∧ beta = z3) ∧
      alpha = beta ∧ alpha = R ∧ R ≠ L) ∨
    (IsBaseMatching2
        (z0 = z1) (z0 = z2) (z0 = alpha ∧ beta = z3)
        (z1 = z2) (z1 = alpha ∧ beta = z3) (z2 = alpha ∧ beta = z3) ∧
      alpha = beta ∧ alpha = R ∧ R = L) := by
  have hmrev : IsBasePerfectMatching
      (z3 = beta ∧ alpha = z2) (z3 = beta ∧ alpha = z1)
      (z3 = beta ∧ alpha = z0) (z2 = z1)
      (z2 = z0) (z1 = z0) := by
    simpa [IsBasePerfectMatching, IsBaseMatching0, IsBaseMatching1,
      IsBaseMatching2, eq_comm, and_comm, and_left_comm, and_assoc] using hmatching
  have hnormal := perfectMatching_sameFirstGap_normalForm
    (L := R) (R := L) (alpha := beta) (beta := alpha)
    (z0 := z3) (z1 := z2) (z2 := z1) (z3 := z0)
    h23.reverse h13.reverse h03.reverse h12.reverse h02.reverse h01.reverse hmrev
  rcases hnormal with h0 | h1 | h2
  · rcases h0 with ⟨hm, hba, hbR⟩
    left
    refine ⟨?_, hba.symm, ?_⟩
    · simpa [IsBaseMatching0, eq_comm, and_comm, and_left_comm, and_assoc] using hm
    · intro haR
      exact hbR (hba.trans haR)
  · rcases h1 with ⟨hm, hba, hbR, hRL⟩
    right
    left
    refine ⟨?_, hba.symm, hba.symm.trans hbR, hRL⟩
    simpa [IsBaseMatching1, eq_comm, and_comm, and_left_comm, and_assoc] using hm
  · rcases h2 with ⟨hm, hba, hbR, hRL⟩
    right
    right
    refine ⟨?_, hba.symm, hba.symm.trans hbR, hRL⟩
    simpa [IsBaseMatching2, eq_comm, and_comm, and_left_comm, and_assoc] using hm

/-- Actual order transport when both owners lie in the last internal base gap. -/
theorem perfectCrossMatching_sameLastGap_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h2o : e 2 < o) (hop : o < p) (hp3 : p < e 3)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let L := χ ⟨e 0, e 1, e 2, e.strictMono (by omega), e.strictMono (by omega)⟩
    let R := χ ⟨e 0, e 2, e 3, e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨e 2, o, e 3, h2o, hop.trans hp3⟩
    let beta := χ ⟨e 2, p, e 3, h2o.trans hop, hp3⟩
    (IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha ≠ R) ∨
    (IsBaseMatching1
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = R ∧ R ≠ L) ∨
    (IsBaseMatching2
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      alpha = beta ∧ alpha = R ∧ R = L) := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h0o : e 0 < o := h02.trans h2o
  have h1o : e 1 < o := h12.trans h2o
  have h2p : e 2 < p := h2o.trans hop
  have h0p : e 0 < p := h0o.trans hop
  have h1p : e 1 < p := h1o.trans hop
  have ho3 : o < e 3 := hop.trans hp3
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 2, o, e 3, h2o, ho3⟩
  let beta : Turn := χ ⟨e 2, p, e 3, h2p, hp3⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨e 1, o, p, h1o, hop⟩
  let z2 : Turn := χ ⟨e 2, o, p, h2o, hop⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho01 : χ ⟨e 0, e 1, o, h01, h1o⟩ = L := by
    simpa [L] using hmo h01 h01 h1o h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho02 : χ ⟨e 0, e 2, o, h02, h2o⟩ = R := by
    simpa [R] using hmo h02 h02 h2o h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, e 2, p, h02, h2p⟩ = R := by
    simpa [R] using hmp h02 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho12 : χ ⟨e 1, e 2, o, h12, h2o⟩ = R := by
    simpa [R] using hmo h12 h02 h2o h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨e 1, e 2, p, h12, h2p⟩ = R := by
    simpa [R] using hmp h12 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨e 0, o, e 3, h0o, ho3⟩ = alpha := by
    simpa [alpha] using hmo h0o h2o ho3 ho3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using hmp h0p h2p hp3 hp3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨e 1, o, e 3, h1o, ho3⟩ = alpha := by
    simpa [alpha] using hmo h1o h2o ho3 ho3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, p, e 3, h1p, hp3⟩ = beta := by
    simpa [beta] using hmp h1p h2p hp3 hp3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ha01 : TurnSequenceAllowed L L z0 z1 := by
    simpa [L, z0, z1, ho01, hp01] using
      hone h01 h1o hop (by simp) (by simp) (by simp) (by simp)
  have ha02 : TurnSequenceAllowed R R z0 z2 := by
    simpa [R, z0, z2, ho02, hp02] using
      hone h02 h2o hop (by simp) (by simp) (by simp) (by simp)
  have ha03 : TurnSequenceAllowed z0 alpha beta z3 := by
    simpa [z0, alpha, beta, z3, ho03, hp03] using
      hone h0o hop hp3 (by simp) (by simp) (by simp) (by simp)
  have ha12 : TurnSequenceAllowed R R z1 z2 := by
    simpa [R, z1, z2, ho12, hp12] using
      hone h12 h2o hop (by simp) (by simp) (by simp) (by simp)
  have ha13 : TurnSequenceAllowed z1 alpha beta z3 := by
    simpa [z1, alpha, beta, z3, ho13, hp13] using
      hone h1o hop hp3 (by simp) (by simp) (by simp) (by simp)
  have ha23 : TurnSequenceAllowed z2 alpha beta z3 := by
    simpa [z2, alpha, beta, z3] using
      hone h2o hop hp3 (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = z1 := by
    change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ z0 = z1
    rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {e 0, e 1, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
        or_assoc]]
    simpa [z0, z1, L, ho01, hp01] using
      (isStrongPolygonSet_four_iff (χ := χ) h01 h1o hop)
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = z2 := by
    change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ z0 = z2
    rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {e 0, e 2, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
        or_assoc]]
    simpa [z0, z2, R, ho02, hp02] using
      (isStrongPolygonSet_four_iff (χ := χ) h02 h2o hop)
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ beta = z3 := by
    simpa [StrongCrossEdge, z0, alpha, beta, z3, ho03, hp03,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp3)
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = z2 := by
    change IsStrongPolygonSet χ {o, p, e 1, e 2} ↔ z1 = z2
    rw [show ({o, p, e 1, e 2} : Finset (Fin n)) = {e 1, e 2, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
        or_assoc]]
    simpa [z1, z2, R, ho12, hp12] using
      (isStrongPolygonSet_four_iff (χ := χ) h12 h2o hop)
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = alpha ∧ beta = z3 := by
    simpa [StrongCrossEdge, z1, alpha, beta, z3, ho13, hp13,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h1o hop hp3)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = alpha ∧ beta = z3 := by
    simpa [StrongCrossEdge, z2, alpha, beta, z3, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) h2o hop hp3)
  have hpure : IsBasePerfectMatching
      (z0 = z1) (z0 = z2) (z0 = alpha ∧ beta = z3)
      (z1 = z2) (z1 = alpha ∧ beta = z3) (z2 = alpha ∧ beta = z3) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using hmatching
  have hnormal := perfectMatching_sameLastGap_normalForm
    ha01 ha02 ha03 ha12 ha13 ha23 hpure
  simpa [L, R, alpha, beta, IsBaseMatching0, IsBaseMatching1,
    IsBaseMatching2, he01, he02, he03, he12, he13, he23] using hnormal

/-- Owners in separated sweep gaps `03` cannot induce a perfect cross
matching on the ordered four-base. -/
theorem not_perfectCrossMatching_gap03
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (ho0 : o < e 0) (h2p : e 2 < p) (hp3 : p < e 3)
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e))) :
    ¬ IsPerfectCrossMatching χ e o p := by
  classical
  intro hmatching
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have ho1 : o < e 1 := ho0.trans h01
  have ho2 : o < e 2 := ho0.trans h02
  have h0p : e 0 < p := h02.trans h2p
  have h1p : e 1 < p := h12.trans h2p
  have hop : o < p := ho0.trans h0p
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨o, e 0, e 1, ho0, h01⟩
  let beta : Turn := χ ⟨e 2, p, e 3, h2p, hp3⟩
  let z0 : Turn := χ ⟨o, e 0, p, ho0, h0p⟩
  let z1 : Turn := χ ⟨o, e 1, p, ho1, h1p⟩
  let z2 : Turn := χ ⟨o, e 2, p, ho2, h2p⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨o, e 0, e 2, ho0, h02⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 h02 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨o, e 0, e 3, ho0, h02.trans h23⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 (h02.trans h23) h01 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h12.trans h23⟩ = L := by
    simpa [L] using hmo ho1 h01 (h12.trans h23) h12 (by simp) (by simp)
      (by simp) (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, e 2, p, h02, h2p⟩ = R := by
    simpa [R] using hmp h02 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨e 1, e 2, p, h12, h2p⟩ = R := by
    simpa [R] using hmp h12 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using hmp h0p h2p hp3 hp3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, p, e 3, h1p, hp3⟩ = beta := by
    simpa [beta] using hmp h1p h2p hp3 hp3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ z1 = L := by
    have hraw : StrongCrossEdge χ e o p 0 1 ↔ alpha = z0 ∧ z1 = L := by
      change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ alpha = z0 ∧ z1 = L
      rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {o, e 0, e 1, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [alpha, z0, z1, L, hp01] using
        (isStrongPolygonSet_four_iff (χ := χ) ho0 h01 h1p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 0 2 ↔ alpha = z0 ∧ z2 = R := by
      change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ alpha = z0 ∧ z2 = R
      rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {o, e 0, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [alpha, z0, z2, R, ho02, hp02] using
        (isStrongPolygonSet_four_iff (χ := χ) ho0 h02 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    simpa [StrongCrossEdge, z0, alpha, z3, beta, ho03, hp03,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho0 h0p hp3)
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = L ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 1 2 ↔ L = z1 ∧ z2 = R := by
      change IsStrongPolygonSet χ {o, p, e 1, e 2} ↔ L = z1 ∧ z2 = R
      rw [show ({o, p, e 1, e 2} : Finset (Fin n)) = {o, e 1, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [L, z1, z2, R, ho12, hp12] using
        (isStrongPolygonSet_four_iff (χ := χ) ho1 h12 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = L ∧ z3 = beta := by
    simpa [StrongCrossEdge, z1, L, z3, beta, ho13, hp13,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho1 h1p hp3)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = R ∧ z3 = beta := by
    simpa [StrongCrossEdge, z2, R, z3, beta, ho23, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho2 h2p hp3)
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = R)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = R)
      (z1 = L ∧ z3 = beta) (z2 = R ∧ z3 = beta) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using
      hmatching
  exact (not_perfectMatching_activeClique
    (P0 := z0 = alpha) (P1 := z1 = L) (P2 := z2 = R) (P3 := z3 = beta)) hpure

/-- Owners in the two exterior sweep gaps `04` cannot induce a perfect cross
matching on the ordered four-base. -/
theorem not_perfectCrossMatching_gap04
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (ho0 : o < e 0) (h3p : e 3 < p)
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e))) :
    ¬ IsPerfectCrossMatching χ e o p := by
  classical
  intro hmatching
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h03 : e 0 < e 3 := h02.trans h23
  have h13 : e 1 < e 3 := h12.trans h23
  have ho1 : o < e 1 := ho0.trans h01
  have ho2 : o < e 2 := ho0.trans h02
  have ho3 : o < e 3 := ho0.trans h03
  have h0p : e 0 < p := h03.trans h3p
  have h1p : e 1 < p := h13.trans h3p
  have h2p : e 2 < p := h23.trans h3p
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨o, e 0, e 1, ho0, h01⟩
  let beta : Turn := χ ⟨e 2, e 3, p, h23, h3p⟩
  let z0 : Turn := χ ⟨o, e 0, p, ho0, h0p⟩
  let z1 : Turn := χ ⟨o, e 1, p, ho1, h1p⟩
  let z2 : Turn := χ ⟨o, e 2, p, ho2, h2p⟩
  let z3 : Turn := χ ⟨o, e 3, p, ho3, h3p⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨o, e 0, e 2, ho0, h02⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 h02 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨o, e 0, e 3, ho0, h03⟩ = alpha := by
    simpa [alpha] using hmo ho0 ho0 h03 h01 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h13⟩ = L := by
    simpa [L] using hmo ho1 h01 h13 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, e 2, p, h02, h2p⟩ = R := by
    simpa [R] using hmp h02 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨e 1, e 2, p, h12, h2p⟩ = R := by
    simpa [R] using hmp h12 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, e 3, p, h03, h3p⟩ = beta := by
    simpa [beta] using hmp h03 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, e 3, p, h13, h3p⟩ = beta := by
    simpa [beta] using hmp h13 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ z1 = L := by
    have hraw : StrongCrossEdge χ e o p 0 1 ↔ alpha = z0 ∧ z1 = L := by
      change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ alpha = z0 ∧ z1 = L
      rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {o, e 0, e 1, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [alpha, z0, z1, L, hp01] using
        (isStrongPolygonSet_four_iff (χ := χ) ho0 h01 h1p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 0 2 ↔ alpha = z0 ∧ z2 = R := by
      change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ alpha = z0 ∧ z2 = R
      rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {o, e 0, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [alpha, z0, z2, R, ho02, hp02] using
        (isStrongPolygonSet_four_iff (χ := χ) ho0 h02 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 0 3 ↔ alpha = z0 ∧ z3 = beta := by
      change IsStrongPolygonSet χ {o, p, e 0, e 3} ↔ alpha = z0 ∧ z3 = beta
      rw [show ({o, p, e 0, e 3} : Finset (Fin n)) = {o, e 0, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [alpha, z0, z3, beta, ho03, hp03] using
        (isStrongPolygonSet_four_iff (χ := χ) ho0 h03 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = L ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 1 2 ↔ L = z1 ∧ z2 = R := by
      change IsStrongPolygonSet χ {o, p, e 1, e 2} ↔ L = z1 ∧ z2 = R
      rw [show ({o, p, e 1, e 2} : Finset (Fin n)) = {o, e 1, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [L, z1, z2, R, ho12, hp12] using
        (isStrongPolygonSet_four_iff (χ := χ) ho1 h12 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = L ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 1 3 ↔ L = z1 ∧ z3 = beta := by
      change IsStrongPolygonSet χ {o, p, e 1, e 3} ↔ L = z1 ∧ z3 = beta
      rw [show ({o, p, e 1, e 3} : Finset (Fin n)) = {o, e 1, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [L, z1, z3, beta, ho13, hp13] using
        (isStrongPolygonSet_four_iff (χ := χ) ho1 h13 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = R ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 2 3 ↔ R = z2 ∧ z3 = beta := by
      change IsStrongPolygonSet χ {o, p, e 2, e 3} ↔ R = z2 ∧ z3 = beta
      rw [show ({o, p, e 2, e 3} : Finset (Fin n)) = {o, e 2, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]]
      simpa [R, z2, z3, beta, ho23] using
        (isStrongPolygonSet_four_iff (χ := χ) ho2 h23 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = R)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = R)
      (z1 = L ∧ z3 = beta) (z2 = R ∧ z3 = beta) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using
      hmatching
  exact (not_perfectMatching_activeClique
    (P0 := z0 = alpha) (P1 := z1 = L) (P2 := z2 = R) (P3 := z3 = beta)) hpure

/-- Owners in separated sweep gaps `13` cannot induce a perfect cross
matching on the ordered four-base. -/
theorem not_perfectCrossMatching_gap13
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h0o : e 0 < o) (ho1 : o < e 1) (h2p : e 2 < p) (hp3 : p < e 3)
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e))) :
    ¬ IsPerfectCrossMatching χ e o p := by
  classical
  intro hmatching
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h13 : e 1 < e 3 := h12.trans h23
  have ho2 : o < e 2 := ho1.trans h12
  have ho3 : o < e 3 := ho2.trans h23
  have h0p : e 0 < p := h02.trans h2p
  have h1p : e 1 < p := h12.trans h2p
  have hop : o < p := ho1.trans h1p
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 0, o, e 1, h0o, ho1⟩
  let beta : Turn := χ ⟨e 2, p, e 3, h2p, hp3⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨o, e 1, p, ho1, h1p⟩
  let z2 : Turn := χ ⟨o, e 2, p, ho2, h2p⟩
  let z3 : Turn := χ ⟨o, p, e 3, hop, hp3⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨e 0, o, e 2, h0o, ho2⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho2 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho03 : χ ⟨e 0, o, e 3, h0o, ho3⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho3 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h13⟩ = L := by
    simpa [L] using hmo ho1 h01 h13 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, e 2, p, h02, h2p⟩ = R := by
    simpa [R] using hmp h02 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨e 1, e 2, p, h12, h2p⟩ = R := by
    simpa [R] using hmp h12 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, p, e 3, h0p, hp3⟩ = beta := by
    simpa [beta] using hmp h0p h2p hp3 hp3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, p, e 3, h1p, hp3⟩ = beta := by
    simpa [beta] using hmp h1p h2p hp3 hp3 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ z1 = L := by
    have hraw : StrongCrossEdge χ e o p 0 1 ↔ alpha = z0 ∧ L = z1 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ alpha = z0 ∧ L = z1
      rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {e 0, o, e 1, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z0, L, z1, hp01] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho1 h1p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 0 2 ↔ alpha = z0 ∧ R = z2 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ alpha = z0 ∧ R = z2
      rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {e 0, o, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z0, R, z2, ho02, hp02] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho2 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ beta = z3 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 3} ↔ z0 = alpha ∧ beta = z3
      rw [show ({o, p, e 0, e 3} : Finset (Fin n)) = {e 0, o, p, e 3} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [z0, alpha, beta, z3, ho03, hp03] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o hop hp3)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1, h.2.symm⟩, fun h ↦ ⟨h.1, h.2.symm⟩⟩
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = L ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 1 2 ↔ L = z1 ∧ z2 = R := by
      change IsStrongPolygonSet χ {o, p, e 1, e 2} ↔ L = z1 ∧ z2 = R
      rw [show ({o, p, e 1, e 2} : Finset (Fin n)) = {o, e 1, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [L, z1, z2, R, ho12, hp12] using
        (isStrongPolygonSet_four_iff (χ := χ) ho1 h12 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = L ∧ z3 = beta := by
    simpa [StrongCrossEdge, z1, L, z3, beta, ho13, hp13,
      Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho1 h1p hp3)
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = R ∧ z3 = beta := by
    simpa [StrongCrossEdge, z2, R, z3, beta, ho23, Finset.insert_comm] using
      (isStrongPolygonSet_four_iff (χ := χ) ho2 h2p hp3)
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = R)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = R)
      (z1 = L ∧ z3 = beta) (z2 = R ∧ z3 = beta) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using
      hmatching
  exact (not_perfectMatching_activeClique
    (P0 := z0 = alpha) (P1 := z1 = L) (P2 := z2 = R) (P3 := z3 = beta)) hpure

/-- Actual order transport for a middle-gap owner followed by a gap-four
owner. -/
theorem perfectCrossMatching_gap24_transport
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h1o : e 1 < o) (ho2 : o < e 2) (h3p : e 3 < p)
    (hone : OneChangeOn χ (insert o (insert p (Finset.univ.image e))))
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e)))
    (hmatching : IsPerfectCrossMatching χ e o p) :
    let R := χ ⟨e 0, e 2, e 3,
      e.strictMono (by omega), e.strictMono (by omega)⟩
    let alpha := χ ⟨e 1, o, e 2, h1o, ho2⟩
    let beta := χ ⟨e 2, e 3, p,
      e.strictMono (by omega), h3p⟩
    IsBaseMatching0
        (StrongCrossEdge χ e o p 0 1) (StrongCrossEdge χ e o p 0 2)
        (StrongCrossEdge χ e o p 0 3) (StrongCrossEdge χ e o p 1 2)
        (StrongCrossEdge χ e o p 1 3) (StrongCrossEdge χ e o p 2 3) ∧
      beta = R ∧ beta ≠ alpha := by
  classical
  dsimp only
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h03 : e 0 < e 3 := h02.trans h23
  have h13 : e 1 < e 3 := h12.trans h23
  have h0o : e 0 < o := h01.trans h1o
  have ho3 : o < e 3 := ho2.trans h23
  have h2p : e 2 < p := h23.trans h3p
  have hop : o < p := ho3.trans h3p
  have h1p : e 1 < p := h1o.trans hop
  have h0p : e 0 < p := h0o.trans hop
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 1, o, e 2, h1o, ho2⟩
  let beta : Turn := χ ⟨e 2, e 3, p, h23, h3p⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨e 1, o, p, h1o, hop⟩
  let z2 : Turn := χ ⟨o, e 2, p, ho2, h2p⟩
  let z3 : Turn := χ ⟨o, e 3, p, ho3, h3p⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho01 : χ ⟨e 0, e 1, o, h01, h1o⟩ = L := by
    simpa [L] using hmo h01 h01 h1o h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho02 : χ ⟨e 0, o, e 2, h0o, ho2⟩ = alpha := by
    simpa [alpha] using hmo h0o h1o ho2 ho2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, e 2, p, h02, h2p⟩ = R := by
    simpa [R] using hmp h02 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho03 : χ ⟨e 0, o, e 3, h0o, ho3⟩ = alpha := by
    simpa [alpha] using hmo h0o h1o ho3 ho2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, e 3, p, h03, h3p⟩ = beta := by
    simpa [beta] using hmp h03 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨e 1, e 2, p, h12, h2p⟩ = R := by
    simpa [R] using hmp h12 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨e 1, o, e 3, h1o, ho3⟩ = alpha := by
    simpa [alpha] using hmo h1o h1o ho3 ho2 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, e 3, p, h13, h3p⟩ = beta := by
    simpa [beta] using hmp h13 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ha12 : TurnSequenceAllowed alpha z1 R z2 := by
    simpa [alpha, z1, R, z2, hp12] using
      hone h1o ho2 h2p (by simp) (by simp) (by simp) (by simp)
  have ha13 : TurnSequenceAllowed alpha z1 beta z3 := by
    simpa [alpha, z1, beta, z3, ho13, hp13] using
      hone h1o ho3 h3p (by simp) (by simp) (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = z1 := by
    change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ z0 = z1
    rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {e 0, e 1, o, p} by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
        or_assoc]]
    simpa [z0, z1, L, ho01, hp01] using
      (isStrongPolygonSet_four_iff (χ := χ) h01 h1o hop)
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 0 2 ↔ alpha = z0 ∧ R = z2 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ alpha = z0 ∧ R = z2
      rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {e 0, o, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z0, R, z2, ho02, hp02] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho2 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 0 3 ↔ alpha = z0 ∧ beta = z3 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 3} ↔ alpha = z0 ∧ beta = z3
      rw [show ({o, p, e 0, e 3} : Finset (Fin n)) = {e 0, o, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z0, beta, z3, ho03, hp03] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho3 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = alpha ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 1 2 ↔ alpha = z1 ∧ R = z2 := by
      change IsStrongPolygonSet χ {o, p, e 1, e 2} ↔ alpha = z1 ∧ R = z2
      rw [show ({o, p, e 1, e 2} : Finset (Fin n)) = {e 1, o, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z1, R, z2, hp12] using
        (isStrongPolygonSet_four_iff (χ := χ) h1o ho2 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = alpha ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 1 3 ↔ alpha = z1 ∧ beta = z3 := by
      change IsStrongPolygonSet χ {o, p, e 1, e 3} ↔ alpha = z1 ∧ beta = z3
      rw [show ({o, p, e 1, e 3} : Finset (Fin n)) = {e 1, o, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z1, beta, z3, ho13, hp13] using
        (isStrongPolygonSet_four_iff (χ := χ) h1o ho3 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = R ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 2 3 ↔ R = z2 ∧ z3 = beta := by
      change IsStrongPolygonSet χ {o, p, e 2, e 3} ↔ R = z2 ∧ z3 = beta
      rw [show ({o, p, e 2, e 3} : Finset (Fin n)) = {o, e 2, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [R, z2, z3, beta, ho23] using
        (isStrongPolygonSet_four_iff (χ := χ) ho2 h23 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have hpure : IsBasePerfectMatching
      (z0 = z1) (z0 = alpha ∧ z2 = R) (z0 = alpha ∧ z3 = beta)
      (z1 = alpha ∧ z2 = R) (z1 = alpha ∧ z3 = beta)
      (z2 = R ∧ z3 = beta) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using
      hmatching
  have hm : IsBaseMatching0
      (z0 = z1)
      (z0 = alpha ∧ z2 = R)
      (z0 = alpha ∧ z3 = beta)
      (z1 = alpha ∧ z2 = R)
      (z1 = alpha ∧ z3 = beta)
      (z2 = R ∧ z3 = beta) := by
    rcases hpure with hm | hm | hm
    · exact hm
    · rcases hm with ⟨h02, h13, hn01, _, _, _⟩
      exact (hn01 (h02.1.trans h13.1.symm)).elim
    · rcases hm with ⟨h03, h12, hn01, _, _, _⟩
      exact (hn01 (h03.1.trans h12.1.symm)).elim
  have hcolors : beta = R ∧ beta ≠ alpha := by
    rcases hm with ⟨_, ⟨hz2R, hz3b⟩, _, _, hn12, _⟩
    have hz1a : z1 ≠ alpha := by
      intro hz1
      exact hn12 ⟨hz1, hz2R⟩
    have hz12 : z1 = z2 :=
      ha12.eq_last_of_first_ne_of_last_eq (Ne.symm hz1a) hz2R.symm
    have hz13 : z1 = z3 :=
      ha13.eq_last_of_first_ne_of_last_eq (Ne.symm hz1a) hz3b.symm
    have hz1R : z1 = R := hz12.trans hz2R
    have hz1b : z1 = beta := hz13.trans hz3b
    refine ⟨hz1b.symm.trans hz1R, ?_⟩
    intro hba
    exact hz1a (hz1b.trans hba)
  have hnormal : IsBaseMatching0
      (z0 = z1) (z0 = alpha ∧ z2 = R) (z0 = alpha ∧ z3 = beta)
      (z1 = alpha ∧ z2 = R) (z1 = alpha ∧ z3 = beta)
      (z2 = R ∧ z3 = beta) ∧ beta = R ∧ beta ≠ alpha :=
    ⟨hm, hcolors⟩
  simpa [R, alpha, beta, IsBaseMatching0, he01, he02, he03, he12, he13,
    he23] using hnormal

/-- Owners in separated sweep gaps `14` cannot induce a perfect cross
matching on the ordered four-base. -/
theorem not_perfectCrossMatching_gap14
    {n : ℕ} {χ : TripleColoring n} (e : Fin 4 ↪o Fin n) {o p : Fin n}
    (h0o : e 0 < o) (ho1 : o < e 1) (h3p : e 3 < p)
    (ho : IsStrongPolygonSet χ (insert o (Finset.univ.image e)))
    (hp : IsStrongPolygonSet χ (insert p (Finset.univ.image e))) :
    ¬ IsPerfectCrossMatching χ e o p := by
  classical
  intro hmatching
  have h01 : e 0 < e 1 := e.strictMono (by omega)
  have h12 : e 1 < e 2 := e.strictMono (by omega)
  have h23 : e 2 < e 3 := e.strictMono (by omega)
  have h02 : e 0 < e 2 := h01.trans h12
  have h03 : e 0 < e 3 := h02.trans h23
  have h13 : e 1 < e 3 := h12.trans h23
  have ho2 : o < e 2 := ho1.trans h12
  have ho3 : o < e 3 := ho2.trans h23
  have h1p : e 1 < p := h13.trans h3p
  have h2p : e 2 < p := h23.trans h3p
  have hop : o < p := ho3.trans h3p
  let L : Turn := χ ⟨e 0, e 1, e 2, h01, h12⟩
  let R : Turn := χ ⟨e 0, e 2, e 3, h02, h23⟩
  let alpha : Turn := χ ⟨e 0, o, e 1, h0o, ho1⟩
  let beta : Turn := χ ⟨e 2, e 3, p, h23, h3p⟩
  let z0 : Turn := χ ⟨e 0, o, p, h0o, hop⟩
  let z1 : Turn := χ ⟨o, e 1, p, ho1, h1p⟩
  let z2 : Turn := χ ⟨o, e 2, p, ho2, h2p⟩
  let z3 : Turn := χ ⟨o, e 3, p, ho3, h3p⟩
  have hmo := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp ho
  have hmp := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hp
  have ho02 : χ ⟨e 0, o, e 2, h0o, ho2⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho2 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho03 : χ ⟨e 0, o, e 3, h0o, ho3⟩ = alpha := by
    simpa [alpha] using
      hmo h0o h0o ho3 ho1 (by simp) (by simp) (by simp) (by simp) (by simp)
  have ho12 : χ ⟨o, e 1, e 2, ho1, h12⟩ = L := by
    simpa [L] using hmo ho1 h01 h12 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho13 : χ ⟨o, e 1, e 3, ho1, h13⟩ = L := by
    simpa [L] using hmo ho1 h01 h13 h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have ho23 : χ ⟨o, e 2, e 3, ho2, h23⟩ = R := by
    simpa [R] using hmo ho2 h02 h23 h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp01 : χ ⟨e 0, e 1, p, h01, h1p⟩ = L := by
    simpa [L] using hmp h01 h01 h1p h12 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp02 : χ ⟨e 0, e 2, p, h02, h2p⟩ = R := by
    simpa [R] using hmp h02 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp12 : χ ⟨e 1, e 2, p, h12, h2p⟩ = R := by
    simpa [R] using hmp h12 h02 h2p h23 (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp03 : χ ⟨e 0, e 3, p, h03, h3p⟩ = beta := by
    simpa [beta] using hmp h03 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have hp13 : χ ⟨e 1, e 3, p, h13, h3p⟩ = beta := by
    simpa [beta] using hmp h13 h23 h3p h3p (by simp) (by simp) (by simp)
      (by simp) (by simp)
  have he01 : StrongCrossEdge χ e o p 0 1 ↔ z0 = alpha ∧ z1 = L := by
    have hraw : StrongCrossEdge χ e o p 0 1 ↔ alpha = z0 ∧ L = z1 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 1} ↔ alpha = z0 ∧ L = z1
      rw [show ({o, p, e 0, e 1} : Finset (Fin n)) = {e 0, o, e 1, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z0, L, z1, hp01] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho1 h1p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he02 : StrongCrossEdge χ e o p 0 2 ↔ z0 = alpha ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 0 2 ↔ alpha = z0 ∧ R = z2 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 2} ↔ alpha = z0 ∧ R = z2
      rw [show ({o, p, e 0, e 2} : Finset (Fin n)) = {e 0, o, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z0, R, z2, ho02, hp02] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho2 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he03 : StrongCrossEdge χ e o p 0 3 ↔ z0 = alpha ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 0 3 ↔ alpha = z0 ∧ beta = z3 := by
      change IsStrongPolygonSet χ {o, p, e 0, e 3} ↔ alpha = z0 ∧ beta = z3
      rw [show ({o, p, e 0, e 3} : Finset (Fin n)) = {e 0, o, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [alpha, z0, beta, z3, ho03, hp03] using
        (isStrongPolygonSet_four_iff (χ := χ) h0o ho3 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  have he12 : StrongCrossEdge χ e o p 1 2 ↔ z1 = L ∧ z2 = R := by
    have hraw : StrongCrossEdge χ e o p 1 2 ↔ L = z1 ∧ z2 = R := by
      change IsStrongPolygonSet χ {o, p, e 1, e 2} ↔ L = z1 ∧ z2 = R
      rw [show ({o, p, e 1, e 2} : Finset (Fin n)) = {o, e 1, e 2, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [L, z1, z2, R, ho12, hp12] using
        (isStrongPolygonSet_four_iff (χ := χ) ho1 h12 h2p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he13 : StrongCrossEdge χ e o p 1 3 ↔ z1 = L ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 1 3 ↔ L = z1 ∧ z3 = beta := by
      change IsStrongPolygonSet χ {o, p, e 1, e 3} ↔ L = z1 ∧ z3 = beta
      rw [show ({o, p, e 1, e 3} : Finset (Fin n)) = {o, e 1, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [L, z1, z3, beta, ho13, hp13] using
        (isStrongPolygonSet_four_iff (χ := χ) ho1 h13 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have he23 : StrongCrossEdge χ e o p 2 3 ↔ z2 = R ∧ z3 = beta := by
    have hraw : StrongCrossEdge χ e o p 2 3 ↔ R = z2 ∧ z3 = beta := by
      change IsStrongPolygonSet χ {o, p, e 2, e 3} ↔ R = z2 ∧ z3 = beta
      rw [show ({o, p, e 2, e 3} : Finset (Fin n)) = {o, e 2, e 3, p} by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm,
          or_assoc]]
      simpa [R, z2, z3, beta, ho23] using
        (isStrongPolygonSet_four_iff (χ := χ) ho2 h23 h3p)
    exact hraw.trans
      ⟨fun h ↦ ⟨h.1.symm, h.2⟩, fun h ↦ ⟨h.1.symm, h.2⟩⟩
  have hpure : IsBasePerfectMatching
      (z0 = alpha ∧ z1 = L) (z0 = alpha ∧ z2 = R)
      (z0 = alpha ∧ z3 = beta) (z1 = L ∧ z2 = R)
      (z1 = L ∧ z3 = beta) (z2 = R ∧ z3 = beta) := by
    simpa [IsPerfectCrossMatching, he01, he02, he03, he12, he13, he23] using
      hmatching
  exact (not_perfectMatching_activeClique
    (P0 := z0 = alpha) (P1 := z1 = L) (P2 := z2 = R) (P3 := z3 = beta)) hpure

end ErdosSzekeres

end
