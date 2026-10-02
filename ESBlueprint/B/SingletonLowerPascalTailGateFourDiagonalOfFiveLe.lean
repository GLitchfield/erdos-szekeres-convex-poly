import ErdosSzekeres.StructuralChargingPascalCupBlocks

namespace ErdosSzekeres

/-- Uniform singleton lower Pascal-tail gate on the four-cap diagonal for every k at least five, obtained from the hand-proved ordered two-cup-block induction and the existing gate consumer.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.singletonLowerPascalTailGate_four_diagonal_of_cupBlocks, ErdosSzekeres.diagonalCupBlocksForce4kk_five
@consumer ErdosSzekeres.decomposableStateUpper_all -/
theorem singletonLowerPascalTailGate_four_diagonal_of_five_le {k : ℕ} (hk : 5 ≤ k) : SingletonLowerPascalTailGate 4 k k := by
  have hblocks : DiagonalCupBlocksForce4kk k := by
    classical
    -- H1: induction on the outer span propagates consecutive turns, for either color.
    have chain {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)} {c : Turn}
        (hone : OneChangeOn χ s)
        (hlocal : ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s →
          (∀ x ∈ s, t.i < x → x < t.j → False) →
          (∀ x ∈ s, t.j < x → x < t.k → False) → χ t = c) :
        ∀ t : OrderedTriple n, t.i ∈ s → t.j ∈ s → t.k ∈ s → χ t = c := by
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
    -- A change between the middle entries pins the two outer entries.
    have switch {a b c d : Turn} (h : TurnSequenceAllowed a b c d) (hne : b ≠ c) :
        a = b ∧ c = d := by
      rcases h with h | h | h | h | h | h | h | h <;>
        rcases h with ⟨rfl, rfl, rfl, rfl⟩ <;> simp at hne ⊢
    -- H3: a cup and one cap apex sharing the cup's endpoints form a strong set.
    have apex {n : ℕ} {χ : TripleColoring n} {C : Finset (Fin n)} {l x r : Fin n}
        (hl : l ∈ C) (hr : r ∈ C) (hx : x ∉ C)
        (hmin : ∀ y ∈ C, l ≤ y) (hmax : ∀ y ∈ C, y ≤ r)
        (hlx : l < x) (hxr : x < r)
        (hcup : IsCupSet χ C) (hone : OneChangeOn χ (insert x C))
        (hcap : χ ⟨l, x, r, hlx, hxr⟩ = Turn.right) :
        IsStrongPolygonSet χ (insert x C) := by
      have capR (a : Fin n) (ha : a ∈ C) (hax : a < x) :
          χ ⟨a, x, r, hax, hxr⟩ = Turn.right := by
        rcases eq_or_lt_of_le (hmin a ha) with rfl | hla
        · exact hcap
        · have hleft := hcup ⟨l, a, r, hla, hax.trans hxr⟩ hl ha hr
          have hseq := hone hla hax hxr (by simp [hl]) (by simp [ha])
            (by simp) (by simp [hr])
          have hne : χ ⟨l, a, r, hla, hax.trans hxr⟩ ≠
              χ ⟨l, x, r, hlx, hxr⟩ := by rw [hleft, hcap]; decide
          exact (switch hseq hne).2.symm.trans hcap
      have capMiddle (a b : Fin n) (ha : a ∈ C) (hb : b ∈ C)
          (hax : a < x) (hxb : x < b) :
          χ ⟨a, x, b, hax, hxb⟩ = Turn.right := by
        rcases eq_or_lt_of_le (hmax b hb) with rfl | hbr
        · exact capR a ha hax
        · have hright := capR a ha hax
          have hleft := hcup ⟨a, b, r, hax.trans hxb, hbr⟩ ha hb hr
          have hseq := hone hax hxb hbr (by simp [ha]) (by simp)
            (by simp [hb]) (by simp [hr])
          have hne : χ ⟨a, x, r, hax, hxb.trans hbr⟩ ≠
              χ ⟨a, b, r, hax.trans hxb, hbr⟩ := by rw [hright, hleft]; decide
          exact (switch hseq hne).1.trans hright
      have color (t : OrderedTriple n)
          (hi : t.i ∈ insert x C) (hj : t.j ∈ insert x C) (hk : t.k ∈ insert x C) :
          χ t = if t.j = x then Turn.right else Turn.left := by
        change χ ⟨t.i, t.j, t.k, t.hij, t.hjk⟩ =
          if t.j = x then Turn.right else Turn.left
        by_cases hjx : t.j = x
        · have hiC : t.i ∈ C := by
            simpa [show t.i ≠ x by rw [← hjx]; exact ne_of_lt t.hij] using hi
          have hkC : t.k ∈ C := by
            simpa [show t.k ≠ x by rw [← hjx]; exact ne_of_gt t.hjk] using hk
          simpa [hjx] using capMiddle t.i t.k hiC hkC
            (by simpa [hjx] using t.hij) (by simpa [hjx] using t.hjk)
        · have hjC : t.j ∈ C := by simpa [hjx] using hj
          by_cases hix : t.i = x
          · have hkC : t.k ∈ C := by
              simpa [show t.k ≠ x by rw [← hix]; exact ne_of_gt (t.hij.trans t.hjk)]
                using hk
            have hxj : x < t.j := by simpa [hix] using t.hij
            have hright := capMiddle l t.k hl hkC hlx (hxj.trans t.hjk)
            have hleft := hcup ⟨l, t.j, t.k, hlx.trans hxj, t.hjk⟩ hl hjC hkC
            have hseq := hone hlx hxj t.hjk (by simp [hl]) (by simp)
              (by simp [hjC]) (by simp [hkC])
            have hne : χ ⟨l, x, t.k, hlx, hxj.trans t.hjk⟩ ≠
                χ ⟨l, t.j, t.k, hlx.trans hxj, t.hjk⟩ := by rw [hright, hleft]; decide
            have hturn := (switch hseq hne).2.symm.trans hleft
            simpa [hjx, hix] using hturn
          · have hiC : t.i ∈ C := by simpa [hix] using hi
            by_cases hkx : t.k = x
            · have hjx' : t.j < x := by simpa [hkx] using t.hjk
              have hright := capR t.i hiC (t.hij.trans hjx')
              have hleft := hcup ⟨t.i, t.j, r, t.hij, hjx'.trans hxr⟩ hiC hjC hr
              have hseq := hone t.hij hjx' hxr (by simp [hiC]) (by simp [hjC])
                (by simp) (by simp [hr])
              have hne : χ ⟨t.i, t.j, r, t.hij, hjx'.trans hxr⟩ ≠
                  χ ⟨t.i, x, r, t.hij.trans hjx', hxr⟩ := by rw [hleft, hright]; decide
              have hturn := (switch hseq hne).1.trans hleft
              simpa [hjx, hkx] using hturn
            · have hkC : t.k ∈ C := by simpa [hkx] using hk
              simpa [hjx] using hcup t hiC hjC hkC
      apply FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mpr
      intro i i' j k k' hij hi'j hjk hjk' hi hi' hj hk hk'
      rw [color _ hi hj hk, color _ hi' hj hk']
    -- Four consecutive cap turns produce an actual cap subset of the ambient set.
    have fourCap {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
        (hone : OneChangeOn χ s) {a b c d : Fin n}
        (hab : a < b) (hbc : b < c) (hcd : c < d)
        (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
        (hfirst : χ ⟨a, b, c, hab, hbc⟩ = Turn.right)
        (hlast : χ ⟨b, c, d, hbc, hcd⟩ = Turn.right) :
        ContainsCapSet χ s 4 := by
      let f : Fin 4 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, b, c, d] (by
        apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        fin_cases i
        · simpa using hab
        · simpa using hbc
        · simpa using hcd)
      have hsub : Finset.univ.image f ⊆ s := by
        intro z hz
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
        obtain ⟨i, rfl⟩ := hz
        fin_cases i
        · simpa [f] using ha
        · simpa [f] using hb
        · simpa [f] using hc
        · simpa [f] using hd
      refine ⟨Finset.univ.image f, hsub, ?_, ?_⟩
      · simpa using Finset.card_image_of_injective Finset.univ f.injective
      · exact FinsetPolygon.IsCap.image (isMonochromaticChain_finFour_of_outer_eq f
          (hone.mono hsub) (by simpa [f] using hfirst) (by simpa [f] using hlast))
    -- H2: only one interior middle can be a cap middle when four-caps are absent.
    have shape {n : ℕ} {χ : TripleColoring n} {s : Finset (Fin n)}
        (hone : OneChangeOn χ s) (hstrong : IsStrongPolygonSet χ s)
        (hnoCap : ¬ContainsCapSet χ s 4) :
        IsCupSet χ s ∨ ∃ l x r : Fin n,
          l ∈ s ∧ x ∈ s ∧ r ∈ s ∧
          (∀ y ∈ s, l ≤ y) ∧ (∀ y ∈ s, y ≤ r) ∧
          ∃ (hlx : l < x) (hxr : x < r),
            IsCupSet χ (s.erase x) ∧ χ ⟨l, x, r, hlx, hxr⟩ = Turn.right := by
      by_cases hcup : IsCupSet χ s
      · exact Or.inl hcup
      · right
        have hbad := hcup
        simp only [IsCupSet, not_forall, _root_.not_imp] at hbad
        obtain ⟨t, hi, hj, hk, hneq⟩ := hbad
        have ht : χ t = Turn.right := by
          cases hcol : χ t with
          | left => exact False.elim (hneq hcol)
          | right => rfl
        have hs : s.Nonempty := ⟨t.i, hi⟩
        let l := s.min' hs
        let r := s.max' hs
        let x := t.j
        have hl : l ∈ s := Finset.min'_mem s hs
        have hr : r ∈ s := Finset.max'_mem s hs
        have hx : x ∈ s := hj
        have hmin (y : Fin n) (hy : y ∈ s) : l ≤ y := Finset.min'_le s y hy
        have hmax (y : Fin n) (hy : y ∈ s) : y ≤ r := Finset.le_max' s y hy
        have hlx : l < x := (hmin t.i hi).trans_lt t.hij
        have hxr : x < r := t.hjk.trans_le (hmax t.k hk)
        have hmiddle := FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hstrong
        have hcap : χ ⟨l, x, r, hlx, hxr⟩ = Turn.right :=
          (hmiddle t.hij hlx t.hjk hxr hi hl hx hk hr).symm.trans ht
        have other (y : Fin n) (hy : y ∈ s) (hly : l < y) (hyr : y < r)
            (hyx : y ≠ x) : χ ⟨l, y, r, hly, hyr⟩ = Turn.left := by
          cases hcol : χ ⟨l, y, r, hly, hyr⟩ with
          | left => rfl
          | right =>
              exfalso
              apply hnoCap
              rcases lt_or_gt_of_ne hyx with hyx' | hxy
              · exact fourCap hone hly hyx' hxr hl hy hx hr
                  ((hmiddle hly hly hyx' hyr hl hl hy hx hr).trans hcol)
                  ((hmiddle hyx' hlx hxr hxr hy hl hx hr hr).trans hcap)
              · exact fourCap hone hlx hxy hyr hl hx hy hr
                  ((hmiddle hlx hlx hxy hxr hl hl hx hy hr).trans hcap)
                  ((hmiddle hxy hly hyr hyr hx hl hy hr hr).trans hcol)
        refine ⟨l, x, r, hl, hx, hr, hmin, hmax, hlx, hxr, ?_, hcap⟩
        intro u hui huj huk
        have hi' := (Finset.mem_erase.mp hui).2
        have hj' := (Finset.mem_erase.mp huj).2
        have hk' := (Finset.mem_erase.mp huk).2
        have hlj : l < u.j := (hmin u.i hi').trans_lt u.hij
        have hjr : u.j < r := u.hjk.trans_le (hmax u.k hk')
        exact (hmiddle u.hij hlj u.hjk hjr hi' hl hj' hk' hr).trans
          (other u.j hj' hlj hjr (Finset.mem_erase.mp huj).1)
    -- M1 and M2: two left cup vertices above a new point shield every new triple.
    have insertLeft {n : ℕ} {χ : TripleColoring n}
        {left right C : Finset (Fin n)} {p a b : Fin n}
        (horder : ∀ u ∈ left, ∀ v ∈ right, u < v)
        (hleft : IsCupSet χ left) (hcup : IsCupSet χ C)
        (hone : OneChangeOn χ (left ∪ right)) (hsub : C ⊆ left ∪ right)
        (hp : p ∈ left) (ha : a ∈ C) (haL : a ∈ left)
        (hb : b ∈ C) (hbL : b ∈ left) (hpa : p < a) (hab : a < b) :
        IsCupSet χ (insert p C) := by
      have hnew : insert p C ⊆ left ∪ right :=
        Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left right hp, hsub⟩
      have leftOfLe (z : Fin n) (hz : z ∈ insert p C) (hzb : z ≤ b) : z ∈ left := by
        rcases Finset.mem_union.mp (hnew hz) with hzL | hzR
        · exact hzL
        · exact False.elim ((not_lt_of_ge hzb) (horder b hbL z hzR))
      apply chain (hone.mono hnew)
      intro t hi hj hk hgap1 hgap2
      have finish (hkb : t.k ≤ b) : χ t = Turn.left := by
        exact hleft t (leftOfLe t.i hi ((t.hij.trans t.hjk).le.trans hkb))
          (leftOfLe t.j hj (t.hjk.le.trans hkb)) (leftOfLe t.k hk hkb)
      by_cases hip : t.i = p
      · apply finish
        by_contra hkb
        have hbk : b < t.k := lt_of_not_ge hkb
        have hja : t.j ≤ a := by
          by_contra hja
          exact hgap1 a (by simp [ha]) (by simpa [hip] using hpa) (lt_of_not_ge hja)
        exact hgap2 b (by simp [hb]) (hja.trans_lt hab) hbk
      · have hiC : t.i ∈ C := by simpa [hip] using hi
        by_cases hjp : t.j = p
        · apply finish
          have hka : t.k ≤ a := by
            by_contra hka
            exact hgap2 a (by simp [ha]) (by simpa [hjp] using hpa) (lt_of_not_ge hka)
          exact hka.trans hab.le
        · have hjC : t.j ∈ C := by simpa [hjp] using hj
          by_cases hkp : t.k = p
          · exact finish (by simpa [hkp] using (hpa.trans hab).le)
          · exact hcup t hiC hjC (by simpa [hkp] using hk)
    -- The mirror move on the right cup uses two selected vertices below the new point.
    have insertRight {n : ℕ} {χ : TripleColoring n}
        {left right C : Finset (Fin n)} {p a b : Fin n}
        (horder : ∀ u ∈ left, ∀ v ∈ right, u < v)
        (hright : IsCupSet χ right) (hcup : IsCupSet χ C)
        (hone : OneChangeOn χ (left ∪ right)) (hsub : C ⊆ left ∪ right)
        (hp : p ∈ right) (ha : a ∈ C) (haR : a ∈ right)
        (hb : b ∈ C) (hbR : b ∈ right) (hab : a < b) (hbp : b < p) :
        IsCupSet χ (insert p C) := by
      have hnew : insert p C ⊆ left ∪ right :=
        Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right left hp, hsub⟩
      have rightOfGe (z : Fin n) (hz : z ∈ insert p C) (haz : a ≤ z) : z ∈ right := by
        rcases Finset.mem_union.mp (hnew hz) with hzL | hzR
        · exact False.elim ((not_lt_of_ge haz) (horder z hzL a haR))
        · exact hzR
      apply chain (hone.mono hnew)
      intro t hi hj hk hgap1 hgap2
      have finish (hai : a ≤ t.i) : χ t = Turn.left := by
        exact hright t (rightOfGe t.i hi hai) (rightOfGe t.j hj (hai.trans t.hij.le))
          (rightOfGe t.k hk (hai.trans (t.hij.trans t.hjk).le))
      by_cases hkp : t.k = p
      · apply finish
        by_contra hai
        have hia : t.i < a := lt_of_not_ge hai
        have hbj : b ≤ t.j := by
          by_contra hbj
          exact hgap2 b (by simp [hb]) (lt_of_not_ge hbj) (by simpa [hkp] using hbp)
        exact hgap1 a (by simp [ha]) hia (hab.trans_le hbj)
      · have hkC : t.k ∈ C := by simpa [hkp] using hk
        by_cases hjp : t.j = p
        · apply finish
          have hbi : b ≤ t.i := by
            by_contra hbi
            exact hgap1 b (by simp [hb]) (lt_of_not_ge hbi) (by simpa [hjp] using hbp)
          exact hab.le.trans hbi
        · have hjC : t.j ∈ C := by simpa [hjp] using hj
          by_cases hip : t.i = p
          · exact finish (by simpa [hip] using (hab.trans hbp).le)
          · exact hcup t (by simpa [hip] using hi) hjC hkC
    have pair {n : ℕ} (s : Finset (Fin n)) (hcard : 2 ≤ s.card) :
        ∃ a ∈ s, ∃ b ∈ s, a < b := by
      let f := s.orderEmbOfCardLe hcard
      exact ⟨f 0, s.orderEmbOfCardLe_mem hcard 0,
        f 1, s.orderEmbOfCardLe_mem hcard 1, f.strictMono (by decide)⟩
    have splitCard {n : ℕ} {left right C : Finset (Fin n)}
        (hdis : Disjoint left right) (hsub : C ⊆ left ∪ right) :
        (C ∩ left).card + (C ∩ right).card = C.card := by
      rw [← Finset.card_union_of_disjoint
        (hdis.mono Finset.inter_subset_right Finset.inter_subset_right),
        ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hsub]
    -- Claim D in a form independent of any particular choice of order enumeration.
    have deletion {n : ℕ} {χ : TripleColoring n} {left right S : Finset (Fin n)}
        {p₀ p q q₀ : Fin n}
        (hdis : Disjoint left right) (horder : ∀ u ∈ left, ∀ v ∈ right, u < v)
        (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
        (hone : OneChangeOn χ (left ∪ right)) (hnoCap : ¬ContainsCapSet χ (left ∪ right) 4)
        (hp₀ : p₀ ∈ left) (hp : p ∈ left) (hp₀p : p₀ < p)
        (hsecond : ∀ y ∈ left, y ≠ p₀ → p ≤ y)
        (hq : q ∈ right) (hq₀ : q₀ ∈ right) (hqq₀ : q < q₀)
        (hpenultimate : ∀ y ∈ right, y ≠ q₀ → y ≤ q)
        (hsub : S ⊆ left ∪ right) (hstrong : IsStrongPolygonSet χ S)
        (hcard : 5 ≤ S.card) (hpNot : p ∉ S) (hqNot : q ∉ S) :
        ContainsStrongPolygonSet χ (left ∪ right) (S.card + 1) := by
      by_contra hnext
      have cupResult (T : Finset (Fin n)) (hTsub : T ⊆ left ∪ right)
          (hTcard : T.card = S.card + 1) (hTcup : IsCupSet χ T) : False :=
        hnext ⟨T, hTsub, hTcard, FinsetPolygon.IsCupSet.isStrongPolygonSet hTcup⟩
      have abovePair (C : Finset (Fin n)) (havoid : p ∉ C)
          (hCcard : 3 ≤ (C ∩ left).card) :
          ∃ a ∈ C, ∃ b ∈ C, a ∈ left ∧ b ∈ left ∧ p < a ∧ a < b := by
        have hdrop := Finset.pred_card_le_card_erase (s := C ∩ left) (a := p₀)
        obtain ⟨a, ha, b, hb, hab⟩ := pair ((C ∩ left).erase p₀) (by omega)
        obtain ⟨ha₀, haC, haL⟩ := by
          simpa only [Finset.mem_erase, Finset.mem_inter, and_assoc] using ha
        obtain ⟨_, hbC, hbL⟩ := by
          simpa only [Finset.mem_erase, Finset.mem_inter, and_assoc] using hb
        have hpa := hsecond a haL ha₀
        have hane : a ≠ p := fun heq ↦ havoid (heq ▸ haC)
        exact ⟨a, haC, b, hbC, haL, hbL, by omega, hab⟩
      have belowPair (C : Finset (Fin n)) (havoid : q ∉ C)
          (hCcard : 3 ≤ (C ∩ right).card) :
          ∃ a ∈ C, ∃ b ∈ C, a ∈ right ∧ b ∈ right ∧ a < b ∧ b < q := by
        have hdrop := Finset.pred_card_le_card_erase (s := C ∩ right) (a := q₀)
        obtain ⟨a, ha, b, hb, hab⟩ := pair ((C ∩ right).erase q₀) (by omega)
        obtain ⟨_, haC, haR⟩ := by
          simpa only [Finset.mem_erase, Finset.mem_inter, and_assoc] using ha
        obtain ⟨hb₀, hbC, hbR⟩ := by
          simpa only [Finset.mem_erase, Finset.mem_inter, and_assoc] using hb
        have hbq := hpenultimate b hbR hb₀
        have hbne : b ≠ q := fun heq ↦ havoid (heq ▸ hbC)
        exact ⟨a, haC, b, hbC, haR, hbR, hab, by omega⟩
      rcases shape (hone.mono hsub) hstrong
          (fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)) with
        hcup | ⟨l, x, r, hl, hx, hr, hmin, hmax, hlx, hxr, hcup, hcap⟩
      · by_cases hL : 3 ≤ (S ∩ left).card
        · obtain ⟨a, ha, b, hb, haL, hbL, hpa, hab⟩ := abovePair S hpNot hL
          exact cupResult (insert p S)
            (Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left right hp, hsub⟩)
            (by simp [Finset.card_insert_of_notMem hpNot])
            (insertLeft horder hleft hcup hone hsub hp ha haL hb hbL hpa hab)
        · by_cases hR : 3 ≤ (S ∩ right).card
          · obtain ⟨a, ha, b, hb, haR, hbR, hab, hbq⟩ := belowPair S hqNot hR
            exact cupResult (insert q S)
              (Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right left hq, hsub⟩)
              (by simp [Finset.card_insert_of_notMem hqNot])
              (insertRight horder hright hcup hone hsub hq ha haR hb hbR hab hbq)
          · have hparts := splitCard hdis hsub
            omega
      · let C := S.erase x
        have hCsub : C ⊆ left ∪ right := Finset.erase_subset x S |>.trans hsub
        have hCcard : C.card + 1 = S.card := Finset.card_erase_add_one hx
        have hxC : x ∉ C := Finset.notMem_erase x S
        have hlC : l ∈ C := Finset.mem_erase.mpr ⟨ne_of_lt hlx, hl⟩
        have hrC : r ∈ C := Finset.mem_erase.mpr ⟨ne_of_gt hxr, hr⟩
        have hpC : p ∉ C := fun hmem ↦ hpNot (Finset.mem_of_mem_erase hmem)
        have hqC : q ∉ C := fun hmem ↦ hqNot (Finset.mem_of_mem_erase hmem)
        have hminC (y : Fin n) (hy : y ∈ C) : l ≤ y :=
          hmin y (Finset.mem_of_mem_erase hy)
        have hmaxC (y : Fin n) (hy : y ∈ C) : y ≤ r :=
          hmax y (Finset.mem_of_mem_erase hy)
        have minLeft (y : Fin n) (hy : y ∈ left ∪ right) : p₀ ≤ y := by
          rcases Finset.mem_union.mp hy with hyL | hyR
          · by_cases hy₀ : y = p₀
            · exact hy₀.ge
            · exact hp₀p.le.trans (hsecond y hyL hy₀)
          · exact (horder p₀ hp₀ y hyR).le
        have maxRight (y : Fin n) (hy : y ∈ left ∪ right) : y ≤ q₀ := by
          rcases Finset.mem_union.mp hy with hyL | hyR
          · exact (horder y hyL q₀ hq₀).le
          · by_cases hy₀ : y = q₀
            · exact hy₀.le
            · exact (hpenultimate y hyR hy₀).trans hqq₀.le
        -- Two cup vertices force the corresponding endpoint, since otherwise two points prepend.
        have endpointLeft (hL : 2 ≤ (C ∩ left).card) : l = p₀ := by
          by_contra hl₀
          have hp₀C : p₀ ∉ C := by
            intro hmem
            exact hl₀ (le_antisymm (hminC p₀ hmem) (minLeft l (hsub hl)))
          obtain ⟨a, ha, b, hb, hab⟩ := pair (C ∩ left) hL
          obtain ⟨haC, haL⟩ := Finset.mem_inter.mp ha
          obtain ⟨hbC, hbL⟩ := Finset.mem_inter.mp hb
          have hpa : p < a := by
            have hle := hsecond a haL (fun heq ↦ hp₀C (heq ▸ haC))
            have hne : a ≠ p := fun heq ↦ hpC (heq ▸ haC)
            omega
          have hcupP := insertLeft horder hleft hcup hone hCsub hp haC haL hbC hbL hpa hab
          have hsubP : insert p C ⊆ left ∪ right :=
            Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left right hp, hCsub⟩
          have hcupPP := insertLeft horder hleft hcupP hone hsubP hp₀
            (Finset.mem_insert_of_mem haC) haL (Finset.mem_insert_of_mem hbC) hbL
            (hp₀p.trans hpa) hab
          exact cupResult (insert p₀ (insert p C))
            (Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left right hp₀, hsubP⟩)
            (by rw [Finset.card_insert_of_notMem (by simp [ne_of_lt hp₀p, hp₀C]),
                Finset.card_insert_of_notMem hpC]; omega) hcupPP
        have endpointRight (hR : 2 ≤ (C ∩ right).card) : r = q₀ := by
          by_contra hr₀
          have hq₀C : q₀ ∉ C := by
            intro hmem
            exact hr₀ (le_antisymm (maxRight r (hsub hr)) (hmaxC q₀ hmem))
          obtain ⟨a, ha, b, hb, hab⟩ := pair (C ∩ right) hR
          obtain ⟨haC, haR⟩ := Finset.mem_inter.mp ha
          obtain ⟨hbC, hbR⟩ := Finset.mem_inter.mp hb
          have hbq : b < q := by
            have hle := hpenultimate b hbR (fun heq ↦ hq₀C (heq ▸ hbC))
            have hne : b ≠ q := fun heq ↦ hqC (heq ▸ hbC)
            omega
          have hcupQ := insertRight horder hright hcup hone hCsub hq haC haR hbC hbR hab hbq
          have hsubQ : insert q C ⊆ left ∪ right :=
            Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right left hq, hCsub⟩
          have hcupQQ := insertRight horder hright hcupQ hone hsubQ hq₀
            (Finset.mem_insert_of_mem haC) haR (Finset.mem_insert_of_mem hbC) hbR
            hab (hbq.trans hqq₀)
          exact cupResult (insert q₀ (insert q C))
            (Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right left hq₀, hsubQ⟩)
            (by rw [Finset.card_insert_of_notMem (by simp [ne_of_gt hqq₀, hq₀C]),
                Finset.card_insert_of_notMem hqC]; omega) hcupQQ
        have apexResult (T : Finset (Fin n)) (hTsub : T ⊆ left ∪ right)
            (hTcard : T.card = S.card) (hTcup : IsCupSet χ T)
            (hlT : l ∈ T) (hrT : r ∈ T) (hxT : x ∉ T)
            (hminT : ∀ y ∈ T, l ≤ y) (hmaxT : ∀ y ∈ T, y ≤ r) : False := by
          have hnew : insert x T ⊆ left ∪ right :=
            Finset.insert_subset_iff.mpr ⟨hsub hx, hTsub⟩
          exact hnext ⟨insert x T, hnew, by simp [Finset.card_insert_of_notMem hxT, hTcard],
            apex hlT hrT hxT hminT hmaxT hlx hxr hTcup (hone.mono hnew) hcap⟩
        have insertionResult (y : Fin n) (hy : y ∈ left ∪ right) (hyNot : y ∉ S)
            (hly : l ≤ y) (hyr : y ≤ r) (hnewCup : IsCupSet χ (insert y C)) : False := by
          have hyC : y ∉ C := fun hmem ↦ hyNot (Finset.mem_of_mem_erase hmem)
          apply apexResult (insert y C) (Finset.insert_subset_iff.mpr ⟨hy, hCsub⟩)
            (by rw [Finset.card_insert_of_notMem hyC]; exact hCcard) hnewCup
            (by simp [hlC]) (by simp [hrC])
            (by simp [show x ≠ y from fun heq ↦ hyNot (heq ▸ hx), hxC])
          · intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact hly
            · exact hminC z hz
          · intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · exact hyr
            · exact hmaxC z hz
        by_cases hL : 3 ≤ (C ∩ left).card
        · obtain ⟨a, ha, b, hb, haL, hbL, hpa, hab⟩ := abovePair C hpC hL
          have hl₀ := endpointLeft (by omega)
          exact insertionResult p (Finset.mem_union_left right hp) hpNot
            (by simpa [hl₀] using hp₀p.le) (hpa.le.trans (hmaxC a ha))
            (insertLeft horder hleft hcup hone hCsub hp ha haL hb hbL hpa hab)
        · by_cases hR : 3 ≤ (C ∩ right).card
          · obtain ⟨a, ha, b, hb, haR, hbR, hab, hbq⟩ := belowPair C hqC hR
            have hr₀ := endpointRight (by omega)
            exact insertionResult q (Finset.mem_union_right left hq) hqNot
              ((hminC b hb).trans hbq.le) (by simpa [hr₀] using hqq₀.le)
              (insertRight horder hright hcup hone hCsub hq ha haR hb hbR hab hbq)
          · have hparts := splitCard hdis hCsub
            have hLtwo : (C ∩ left).card = 2 := by omega
            have hRtwo : (C ∩ right).card = 2 := by omega
            have hCfour : C.card = 4 := by omega
            have hl₀ := endpointLeft (by omega)
            have hr₀ := endpointRight (by omega)
            have hp₀C : p₀ ∈ C := by simpa [hl₀] using hlC
            have hq₀C : q₀ ∈ C := by simpa [hr₀] using hrC
            obtain ⟨s, hs, hs₀⟩ := (C ∩ left).exists_mem_ne (by omega) p₀
            obtain ⟨t, ht, ht₀⟩ := (C ∩ right).exists_mem_ne (by omega) q₀
            obtain ⟨hsC, hsL⟩ := Finset.mem_inter.mp hs
            obtain ⟨htC, htR⟩ := Finset.mem_inter.mp ht
            have hps : p < s := by
              have hle := hsecond s hsL hs₀
              have hne : s ≠ p := fun heq ↦ hpC (heq ▸ hsC)
              omega
            have htq : t < q := by
              have hle := hpenultimate t htR ht₀
              have hne : t ≠ q := fun heq ↦ hqC (heq ▸ htC)
              omega
            have hst : s < t := horder s hsL t htR
            have h₀s : p₀ < s := hp₀p.trans hps
            have ht₀ : t < q₀ := htq.trans hqq₀
            have hfourSub : ({p₀, s, t, q₀} : Finset (Fin n)) ⊆ C := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl | rfl
              · exact hp₀C
              · exact hsC
              · exact htC
              · exact hq₀C
            have hfourCard : ({p₀, s, t, q₀} : Finset (Fin n)).card = 4 := by
              simp [ne_of_lt h₀s, ne_of_lt (h₀s.trans hst), ne_of_lt (h₀s.trans (hst.trans ht₀)),
                ne_of_lt hst, ne_of_lt (hst.trans ht₀), ne_of_lt ht₀]
            have hCeq : C = {p₀, s, t, q₀} :=
              (Finset.eq_of_subset_of_card_le hfourSub (by omega)).symm
            cases hpst : χ ⟨p, s, t, hps, hst⟩ with
            | left =>
                let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono ![p₀, p, s, t, q₀] (by
                  apply Fin.strictMono_iff_lt_succ.mpr
                  intro i
                  fin_cases i
                  · simpa using hp₀p
                  · simpa using hps
                  · simpa using hst
                  · simpa using ht₀)
                have himage : Finset.univ.image f = insert p C := by
                  rw [hCeq]
                  ext z
                  simp [f, Fin.exists_fin_succ, eq_comm, or_assoc, or_left_comm, or_comm]
                have hnew : insert p C ⊆ left ∪ right :=
                  Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left right hp, hCsub⟩
                have hchain := isMonochromaticChain_finFive_of_consecutive f
                  (hone.mono (by rw [himage]; exact hnew))
                  (by simpa [f] using hleft ⟨p₀, p, s, hp₀p, hps⟩ hp₀ hp hsL)
                  (by simpa [f] using hpst)
                  (by simpa [f] using hcup ⟨s, t, q₀, hst, ht₀⟩ hsC htC hq₀C)
                exact insertionResult p (Finset.mem_union_left right hp) hpNot
                  (by simpa [hl₀] using hp₀p.le) (by simpa [hr₀] using (horder p hp q₀ hq₀).le)
                  (by simpa only [himage] using FinsetPolygon.IsCup.image hchain)
            | right =>
                cases hstq : χ ⟨s, t, q, hst, htq⟩ with
                | left =>
                    let f : Fin 5 ↪o Fin n := OrderEmbedding.ofStrictMono ![p₀, s, t, q, q₀] (by
                      apply Fin.strictMono_iff_lt_succ.mpr
                      intro i
                      fin_cases i
                      · simpa using h₀s
                      · simpa using hst
                      · simpa using htq
                      · simpa using hqq₀)
                    have himage : Finset.univ.image f = insert q C := by
                      rw [hCeq]
                      ext z
                      simp [f, Fin.exists_fin_succ, eq_comm, or_assoc, or_left_comm, or_comm]
                    have hnew : insert q C ⊆ left ∪ right :=
                      Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right left hq, hCsub⟩
                    have hchain := isMonochromaticChain_finFive_of_consecutive f
                      (hone.mono (by rw [himage]; exact hnew))
                      (by simpa [f] using hcup ⟨p₀, s, t, h₀s, hst⟩ hp₀C hsC htC)
                      (by simpa [f] using hstq)
                      (by simpa [f] using hright ⟨t, q, q₀, htq, hqq₀⟩ htR hq hq₀)
                    exact insertionResult q (Finset.mem_union_right left hq) hqNot
                      (by simpa [hl₀] using (horder p₀ hp₀ q hq).le)
                      (by simpa [hr₀] using hqq₀.le)
                      (by simpa only [himage] using FinsetPolygon.IsCup.image hchain)
                | right =>
                    exact hnoCap (fourCap hone hps hst htq
                      (Finset.mem_union_left right hp) (hCsub hsC) (hCsub htC)
                      (Finset.mem_union_right left hq) hpst hstq)
    have second {n : ℕ} (s : Finset (Fin n)) (hcard : 2 ≤ s.card) :
        ∃ p₀ p : Fin n, p₀ ∈ s ∧ p ∈ s ∧ p₀ < p ∧
          ∀ y ∈ s, y ≠ p₀ → p ≤ y := by
      have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      let p₀ := s.min' hs
      have hp₀ : p₀ ∈ s := Finset.min'_mem s hs
      have hdrop := Finset.card_erase_add_one hp₀
      have hs' : (s.erase p₀).Nonempty := Finset.card_pos.mp (by omega)
      let p := (s.erase p₀).min' hs'
      have hp' : p ∈ s.erase p₀ := Finset.min'_mem _ hs'
      have hp : p ∈ s := Finset.mem_of_mem_erase hp'
      have hp₀p : p₀ < p := by
        have hle : p₀ ≤ p := Finset.min'_le s p hp
        have hne := (Finset.mem_erase.mp hp').1
        omega
      exact ⟨p₀, p, hp₀, hp, hp₀p,
        fun y hy hy₀ ↦ Finset.min'_le (s.erase p₀) y (Finset.mem_erase.mpr ⟨hy₀, hy⟩)⟩
    have penultimate {n : ℕ} (s : Finset (Fin n)) (hcard : 2 ≤ s.card) :
        ∃ q q₀ : Fin n, q ∈ s ∧ q₀ ∈ s ∧ q < q₀ ∧
          ∀ y ∈ s, y ≠ q₀ → y ≤ q := by
      have hs : s.Nonempty := Finset.card_pos.mp (by omega)
      let q₀ := s.max' hs
      have hq₀ : q₀ ∈ s := Finset.max'_mem s hs
      have hdrop := Finset.card_erase_add_one hq₀
      have hs' : (s.erase q₀).Nonempty := Finset.card_pos.mp (by omega)
      let q := (s.erase q₀).max' hs'
      have hq' : q ∈ s.erase q₀ := Finset.max'_mem _ hs'
      have hq : q ∈ s := Finset.mem_of_mem_erase hq'
      have hqq₀ : q < q₀ := by
        have hle : q ≤ q₀ := Finset.le_max' s q hq
        have hne := (Finset.mem_erase.mp hq').1
        omega
      exact ⟨q, q₀, hq, hq₀, hqq₀,
        fun y hy hy₀ ↦ Finset.le_max' (s.erase q₀) y (Finset.mem_erase.mpr ⟨hy₀, hy⟩)⟩
    -- The strengthened cardinality statement makes the induction apply to arbitrary deleted sides.
    have bound : ∀ k : ℕ, 5 ≤ k →
        ∀ {n : ℕ} {χ : TripleColoring n} {left right : Finset (Fin n)},
          Disjoint left right → (∀ u ∈ left, ∀ v ∈ right, u < v) →
          IsCupSet χ left → IsCupSet χ right → OneChangeOn χ (left ∪ right) →
          ¬ContainsCapSet χ (left ∪ right) 4 →
          ¬ContainsStrongPolygonSet χ (left ∪ right) k →
          left.card + right.card ≤ 2 * k - 4 := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
          intro hk n χ left right hdis horder hleft hright hone hnoCap hnoStrong
          by_cases hfive : k = 5
          · subst k
            exact diagonal_cup_block_card_add_le (by omega) diagonalCupBlocksForce4kk_five
              hdis horder hleft hright hone hnoCap
              (fun hcup ↦ hnoStrong (FinsetPolygon.ContainsCupSet.toContainsStrongPolygonSet hcup))
              hnoStrong
          · have sideBound (T : Finset (Fin n)) (hTsub : T ⊆ left ∪ right)
                (hTcup : IsCupSet χ T) : T.card ≤ k - 1 := by
              by_contra hTcard
              obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq (by omega : k ≤ T.card)
              exact hnoStrong ⟨C, hCsub.trans hTsub, hCcard,
                FinsetPolygon.IsCupSet.isStrongPolygonSet
                  (FinsetPolygon.IsCupSet.mono hTcup hCsub)⟩
            have hleftCard := sideBound left Finset.subset_union_left hleft
            have hrightCard := sideBound right Finset.subset_union_right hright
            by_contra hsum
            obtain ⟨p₀, p, hp₀, hp, hp₀p, hsecond⟩ := second left (by omega)
            obtain ⟨q, q₀, hq, hq₀, hqq₀, hpenultimate⟩ := penultimate right (by omega)
            let left' := left.erase p
            let right' := right.erase q
            have hleftSub : left' ⊆ left := Finset.erase_subset p left
            have hrightSub : right' ⊆ right := Finset.erase_subset q right
            have hsub : left' ∪ right' ⊆ left ∪ right :=
              Finset.union_subset_union hleftSub hrightSub
            have hnoStrong' : ¬ContainsStrongPolygonSet χ (left' ∪ right') (k - 1) := by
              rintro ⟨S, hSsub, hScard, hSstrong⟩
              have hpNot : p ∉ S := by
                intro hpS
                rcases Finset.mem_union.mp (hSsub hpS) with hpL | hpR
                · exact Finset.notMem_erase p left hpL
                · exact Finset.disjoint_left.mp hdis hp (hrightSub hpR)
              have hqNot : q ∉ S := by
                intro hqS
                rcases Finset.mem_union.mp (hSsub hqS) with hqL | hqR
                · exact Finset.disjoint_left.mp hdis (hleftSub hqL) hq
                · exact Finset.notMem_erase q right hqR
              have hnext := deletion hdis horder hleft hright hone hnoCap hp₀ hp hp₀p
                hsecond hq hq₀ hqq₀ hpenultimate (hSsub.trans hsub) hSstrong
                (by omega) hpNot hqNot
              apply hnoStrong
              simpa only [hScard, show k - 1 + 1 = k by omega] using hnext
            have hbound := ih (k - 1) (by omega) (by omega)
              (hdis.mono hleftSub hrightSub)
              (fun u hu v hv ↦ horder u (hleftSub hu) v (hrightSub hv))
              (FinsetPolygon.IsCupSet.mono hleft hleftSub)
              (FinsetPolygon.IsCupSet.mono hright hrightSub) (hone.mono hsub)
              (fun hcap ↦ hnoCap (FinsetPolygon.ContainsCapSet.mono hcap hsub)) hnoStrong'
            have hleftErase : left'.card + 1 = left.card := Finset.card_erase_add_one hp
            have hrightErase : right'.card + 1 = right.card := Finset.card_erase_add_one hq
            omega
    intro n χ left right hdis horder hcards hleft hright hone
    by_cases hcap : ContainsCapSet χ (left ∪ right) 4
    · exact Or.inl hcap
    · by_cases hstrong : ContainsStrongPolygonSet χ (left ∪ right) k
      · exact Or.inr (Or.inr hstrong)
      · have hbound := bound k hk hdis horder hleft hright hone hcap hstrong
        rcases hcards with ⟨hL, hR⟩ | ⟨hL, hR⟩ <;> omega
  intro n χ q upper
  exact singletonLowerPascalTailGate_four_diagonal_of_cupBlocks hk hblocks

end ErdosSzekeres
