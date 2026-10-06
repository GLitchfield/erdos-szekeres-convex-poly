import ErdosSzekeres.StructuralChargingCore

namespace ErdosSzekeres

/-- The ordinary binomial cup-cap alternative on an arbitrary finite support under OneChange, without geometric realizability. Reuse the generic consecutive-chain recurrence and propagate consecutive colors through the four-point law.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.CupCap.cup_cap, ErdosSzekeres.TurnSequenceAllowed.all_eq_of_outer_eq
@dangling-ok Approved R20 reusable all-arity counting bridge; replaces repeated fixed-size OneChange promotion recipes, while tight a5 polygon-dependent savings remain open. -/
theorem containsCapSet_or_containsCupSet_of_oneChange_choose_lt {n a u : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
    (hone : OneChangeOn χ s) (ha : 2 ≤ a) (hu : 2 ≤ u)
    (hcard : Nat.choose (a + u - 4) (a - 2) < s.card) :
    ContainsCapSet χ s a ∨ ContainsCupSet χ s u := by
  classical
  have propagate {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {c : Turn}
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
  have promote (color : Turn) {m : ℕ}
      (h : CupCap.HasNChain (CupCap.totalColor χ) color m s) :
      ∃ C : Finset (Fin n), C ⊆ s ∧ C.card = m ∧
        ∀ t : OrderedTriple n, t.i ∈ C → t.j ∈ C → t.k ∈ C → χ t = color := by
    obtain ⟨l, hchain, hlen, hlin⟩ := h
    let f : Fin l.length ↪o Fin n :=
      OrderEmbedding.ofStrictMono l.get hchain.1.sortedLT.strictMono_get
    have hfsub : Finset.univ.image f ⊆ s := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hlin (l.get i) (l.get_mem i)
    have honeRestrict : OneChangeOn (χ.restrict f) Finset.univ := by
      intro i j k l hij hjk hkl _ _ _ _
      simpa [TripleColoring.restrict, OrderedTriple.map] using
        hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
          (hfsub (by simp)) (hfsub (by simp)) (hfsub (by simp)) (hfsub (by simp))
    have hlocal : ∀ t : OrderedTriple l.length,
        t.i ∈ (Finset.univ : Finset (Fin l.length)) → t.j ∈ Finset.univ → t.k ∈ Finset.univ →
        (∀ x ∈ (Finset.univ : Finset (Fin l.length)), t.i < x → x < t.j → False) →
        (∀ x ∈ (Finset.univ : Finset (Fin l.length)), t.j < x → x < t.k → False) →
        χ.restrict f t = color := by
      intro t _ _ _ hgapFirst hgapLast
      have hij : t.i < t.j := t.hij
      have hjk : t.j < t.k := t.hjk
      have hfirst : t.j.val = t.i.val + 1 := by
        by_contra hne
        let x : Fin l.length := ⟨t.i.val + 1, by omega⟩
        have hix : t.i < x := by change t.i.val < t.i.val + 1; omega
        have hxj : x < t.j := by change t.i.val + 1 < t.j.val; omega
        exact hgapFirst x (Finset.mem_univ x) hix hxj
      have hlast : t.k.val = t.j.val + 1 := by
        by_contra hne
        let x : Fin l.length := ⟨t.j.val + 1, by omega⟩
        have hjx : t.j < x := by change t.j.val < t.j.val + 1; omega
        have hxk : x < t.k := by change t.j.val + 1 < t.k.val; omega
        exact hgapLast x (Finset.mem_univ x) hjx hxk
      have hi : t.i.val + 2 < l.length := by omega
      have hturn := CupCap.consecutive'_getElem hchain.2 t.i.val hi
      have hturn' : CupCap.totalColor χ (f t.i) (f t.j) (f t.k) = color := by
        simpa [f, hfirst, hlast] using hturn
      rw [CupCap.totalColor_of_lt χ (f.strictMono t.hij) (f.strictMono t.hjk)] at hturn'
      exact hturn'
    have hall := propagate honeRestrict hlocal
    have hmono : IsMonochromaticChain χ color f := by
      refine ⟨f.strictMono, ?_⟩
      intro i j k hij hjk
      simpa [TripleColoring.restrict, OrderedTriple.map] using
        hall ⟨i, j, k, hij, hjk⟩ (by simp) (by simp) (by simp)
    refine ⟨Finset.univ.image f, hfsub, ?_, ?_⟩
    · exact (Finset.card_image_of_injective _ f.injective).trans (by simpa using hlen)
    · exact FinsetPolygon.IsMonochromaticChain.isMonochromaticSet_image hmono
  have hsum : (a - 2) + (u - 2) = a + u - 4 := by omega
  have ha' : (a - 2) + 2 = a := by omega
  have hu' : (u - 2) + 2 = u := by omega
  have hchoose : Nat.choose ((a - 2) + (u - 2)) (a - 2) < s.card := by
    rwa [hsum]
  rcases CupCap.cup_cap (CupCap.totalColor χ) (a - 2) (u - 2) s hchoose with hcap | hcup
  · obtain ⟨C, hCsub, hCcard, hC⟩ := promote Turn.right hcap
    exact Or.inl ⟨C, hCsub, hCcard.trans ha', hC⟩
  · obtain ⟨C, hCsub, hCcard, hC⟩ := promote Turn.left hcup
    exact Or.inr ⟨C, hCsub, hCcard.trans hu', hC⟩


end ErdosSzekeres
