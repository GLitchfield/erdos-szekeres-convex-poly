import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- Abstract H1: a fixed turn on every support-consecutive triple propagates to every triple under OneChange. The proof is induction on outer span and works for both cup and cap colors.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq
@dangling-ok Approved R20 reusable signotope helper, replaying the accepted uniform proof invariant for cap/cup layer and extension arguments; coupled a5 cut remains open -/
theorem allTripleColors_eq_of_consecutive {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {c : Turn}
    (hone : OneChangeOn χ s)
    (hlocal : ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s →
      (∀ x ∈ s, t.i < x → x < t.j → False) →
      (∀ x ∈ s, t.j < x → x < t.k → False) → χ t = c) :
    ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = c := by
  classical
  have aux : ∀ span : ℕ, ∀ (i j l : Fin n), l.val - i.val = span →
      (hij : i < j) → (hjl : j < l) → i ∈ s → j ∈ s → l ∈ s →
      χ ⟨i, j, l, hij, hjl⟩ = c := by
    intro span
    induction span using Nat.strong_induction_on with
    | h span ih =>
        intro i j l hspan hij hjl hi hj hl
        by_cases hgap : ∃ x ∈ s, i < x ∧ x < j
        · obtain ⟨x, hx, hix, hxj⟩ := hgap
          have hfirst := ih (j.val - i.val) (by omega) i x j rfl hix hxj hi hx hj
          have hlast := ih (l.val - x.val) (by omega) x j l rfl hxj hjl hx hj hl
          have hall := (hone hix hxj hjl hi hx hj hl).all_eq_of_outer_eq
            (hfirst.trans hlast.symm)
          exact hall.2.2.trans hlast
        · by_cases hgap' : ∃ x ∈ s, j < x ∧ x < l
          · obtain ⟨x, hx, hjx, hxl⟩ := hgap'
            have hfirst := ih (x.val - i.val) (by omega) i j x rfl hij hjx hi hj hx
            have hlast := ih (l.val - j.val) (by omega) j x l rfl hjx hxl hj hx hl
            have hall := (hone hij hjx hxl hi hj hx hl).all_eq_of_outer_eq
              (hfirst.trans hlast.symm)
            exact hall.1.symm.trans hfirst
          · exact hlocal _ hi hj hl
              (fun x hx hix hxj ↦ hgap ⟨x, hx, hix, hxj⟩)
              (fun x hx hjx hxl ↦ hgap' ⟨x, hx, hjx, hxl⟩)
  intro t hi hj hl
  exact aux (t.k.val - t.i.val) t.i t.j t.k rfl t.hij t.hjk hi hj hl


end ErdosSzekeres
