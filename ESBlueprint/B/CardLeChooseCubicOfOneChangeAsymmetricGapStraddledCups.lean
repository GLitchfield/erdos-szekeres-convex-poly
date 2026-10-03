import ESBlueprint.B.CardLeTwoChooseCubicOfOneChangeGapNoCapSixStraddledCups

namespace ErdosSzekeres

/-- Audited paired asymmetric marker bounds with global six-cap exclusion retained. Strong WM endpoint exclusion gives a four-cap-free complete endpoint family of at most choose(m,2) points. Deleting it removes every m-cup; paired ZR bounds the complement, including the sharper cup-prefix variant.
@node
@ws B
@kind formalization
@consumer ErdosSzekeres.singletonLowerPascalTailGate_six_pred_pred_of_seven_le -/
theorem card_le_choose_cubic_of_oneChange_asymmetric_gap_straddled_cups {n m : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {q h : Fin n}
(hm : 3 ≤ m) (hq : q ∉ s) (hone : OneChangeOn χ s)
(hleft : ¬ContainsCapSet χ (s.filter (fun x ↦ x < q)) 4)
(hright : ¬ContainsCapSet χ (s.filter (fun x ↦ q < x)) 5)
(hnoCap : ¬ContainsCapSet χ s 6) (hnoCup : ¬ContainsCupSet χ s (m + 1))
(hstraddle : ∀ C : Finset (Fin n), C ⊆ s → C.card = m → IsCupSet χ C →
  (∃ x ∈ C, x < h) ∧ ∃ y ∈ C, h < y) :
s.card ≤ Nat.choose m 2 + Nat.choose (m + 1) 3 + Nat.choose (m - 1) 2 ∧
(IsCupSet χ (s.filter (fun x ↦ x < q)) →
 s.card ≤ Nat.choose m 2 + Nat.choose (m + 1) 3 + (m - 2)) := by
  sorry

end ErdosSzekeres
