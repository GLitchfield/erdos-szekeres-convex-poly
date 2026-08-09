module

public import ErdosSzekeres.StructuralChargingNextState578RestrictedMiddlePairsCounterexample

@[expose] public section

/-!
# The surviving upper-endpoint bracket invariant

Two disjoint lower sweep-middle pairs do not force a state-578 target.  What
survives is their placement relative to upper vertices: under five-cup
avoidance, every lower set lying strictly between two upper vertices is a cap.
Consequently no seven such lower vertices can share an upper bracket when a
seven-cap is also forbidden.
-/

namespace ErdosSzekeres

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000

/-- If a lower set lies strictly between two upper vertices, five-cup
avoidance forces every triple in the lower set to be cap-colored. -/
theorem HasDeepBelowSplit.bracketed_lower_isCapSet_of_no_cupFive
    {n : ℕ} {χ : TripleColoring n}
    {lower upper core : Finset (Fin n)} {left right : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hcoreSub : core ⊆ lower)
    (hleftUpper : left ∈ upper) (hrightUpper : right ∈ upper)
    (hbracket : ∀ x ∈ core, left < x ∧ x < right)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 5) :
    IsCapSet χ core := by
  intro t hti htj htk
  by_cases hright : χ t = .right
  · exact hright
  have hleft : χ t = .left := by
    cases hturn : χ t with
    | left => rfl
    | right => exact (hright hturn).elim
  let tripleSet : Finset (Fin n) := {t.i, t.j, t.k}
  have htripleSubCore : tripleSet ⊆ core := by
    intro x hx
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hti
    · exact htj
    · exact htk
  have htripleSubLower : tripleSet ⊆ lower :=
    htripleSubCore.trans hcoreSub
  have htripleCard : tripleSet.card = 3 := by
    simp [tripleSet, ne_of_lt t.hij, ne_of_lt t.hjk,
      ne_of_lt (t.hij.trans t.hjk)]
  have htripleCup : IsCupSet χ tripleSet := by
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [tripleSet, Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl <;>
          first
          | exact hleft
          | (exfalso; have := t.hij; have := t.hjk; omega)
  have hleftRight : left < right :=
    (hbracket t.i hti).1.trans (hbracket t.i hti).2
  let five := insert left (insert right tripleSet)
  have hleftBound {x : Fin n} (hx : x ∈ five) : left ≤ x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    rcases Finset.mem_insert.mp hx with rfl | hxTriple
    · exact hleftRight.le
    · exact (hbracket x (htripleSubCore hxTriple)).1.le
  have hrightBound {x : Fin n} (hx : x ∈ five) : x ≤ right := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hleftRight.le
    rcases Finset.mem_insert.mp hx with rfl | hxTriple
    · exact le_rfl
    · exact (hbracket x (htripleSubCore hxTriple)).2.le
  have hfiveSub : five ⊆ lower ∪ upper := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_union_right _ hleftUpper
    rcases Finset.mem_insert.mp hx with rfl | hxTriple
    · exact Finset.mem_union_right _ hrightUpper
    · exact Finset.mem_union_left _ (htripleSubLower hxTriple)
  have hfiveCard : five.card = 5 := by
    have hleftNotTriple : left ∉ tripleSet := by
      intro hx
      exact (not_lt_of_ge (hleftBound
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
        (hbracket left (htripleSubCore hx)).1
    have hrightNotTriple : right ∉ tripleSet := by
      intro hx
      exact (not_lt_of_ge (hrightBound
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))))
        (hbracket right (htripleSubCore hx)).2
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem hrightNotTriple, htripleCard]
    · simpa [Finset.mem_insert, hleftRight.ne] using hleftNotTriple
  have hfiveCup : IsCupSet χ five := by
    intro u hui huj huk
    by_cases hallTriple :
        u.i ∈ tripleSet ∧ u.j ∈ tripleSet ∧ u.k ∈ tripleSet
    · exact htripleCup u hallTriple.1 hallTriple.2.1 hallTriple.2.2
    have hjTriple : u.j ∈ tripleSet := by
      rcases Finset.mem_insert.mp huj with hjLeft | hj
      · have hbad : u.i < left := by simpa [hjLeft] using u.hij
        exact (not_lt_of_ge (hleftBound hui) hbad).elim
      rcases Finset.mem_insert.mp hj with hjRight | hjTriple
      · have hbad : right < u.k := by simpa [hjRight] using u.hjk
        exact (not_lt_of_ge (hrightBound huk) hbad).elim
      · exact hjTriple
    have hjLower : u.j ∈ lower := htripleSubLower hjTriple
    have memTriple_of_memFive_of_memLower {x : Fin n}
        (hxFive : x ∈ five) (hxLower : x ∈ lower) : x ∈ tripleSet := by
      rcases Finset.mem_insert.mp hxFive with hxLeft | hx
      · exact ((Finset.disjoint_left.mp hdeep.disjoint) hxLower
          (hxLeft ▸ hleftUpper)).elim
      rcases Finset.mem_insert.mp hx with hxRight | hxTriple
      · exact ((Finset.disjoint_left.mp hdeep.disjoint) hxLower
          (hxRight ▸ hrightUpper)).elim
      · exact hxTriple
    have hnotLower :
        ¬(u.i ∈ lower ∧ u.j ∈ lower ∧ u.k ∈ lower) := by
      rintro ⟨hiLower, hjLower', hkLower⟩
      exact hallTriple ⟨
        memTriple_of_memFive_of_memLower hui hiLower,
        memTriple_of_memFive_of_memLower huj hjLower',
        memTriple_of_memFive_of_memLower huk hkLower⟩
    have hnotUpper :
        ¬(u.i ∈ upper ∧ u.j ∈ upper ∧ u.k ∈ upper) := by
      rintro ⟨_, hjUpper, _⟩
      exact (Finset.disjoint_left.mp hdeep.disjoint) hjLower hjUpper
    simpa [hjLower] using hdeep.crossing u
      (hfiveSub hui) (hfiveSub huj) (hfiveSub huk) hnotLower hnotUpper
  exact (hnoCup ⟨five, hfiveSub, hfiveCard, hfiveCup⟩).elim

/-- The target-free cardinal form: an upper bracket contains at most six
vertices of any lower set when both five-cups and seven-caps are forbidden. -/
theorem HasDeepBelowSplit.bracketed_lower_card_le_six
    {n : ℕ} {χ : TripleColoring n}
    {lower upper core : Finset (Fin n)} {left right : Fin n}
    (hdeep : HasDeepBelowSplit χ lower upper)
    (hcoreSub : core ⊆ lower)
    (hleftUpper : left ∈ upper) (hrightUpper : right ∈ upper)
    (hbracket : ∀ x ∈ core, left < x ∧ x < right)
    (hnoCup : ¬ContainsCupSet χ (lower ∪ upper) 5)
    (hnoCap : ¬ContainsCapSet χ (lower ∪ upper) 7) :
    core.card ≤ 6 := by
  by_contra hlarge
  have hseven : 7 ≤ core.card := by omega
  obtain ⟨seven, hsevenSub, hsevenCard⟩ :=
    Finset.exists_subset_card_eq hseven
  have hcoreCap := hdeep.bracketed_lower_isCapSet_of_no_cupFive
    hcoreSub hleftUpper hrightUpper hbracket hnoCup
  exact hnoCap ⟨seven, hsevenSub.trans
    (hcoreSub.trans Finset.subset_union_left), hsevenCard,
    FinsetPolygon.IsCapSet.mono hcoreCap hsevenSub⟩

end ErdosSzekeres

end
