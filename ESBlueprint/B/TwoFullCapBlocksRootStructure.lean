import ErdosSzekeres.Decomposable

namespace ErdosSzekeres

/-- At a nonempty deep-below root splitting the union of two disjoint full p-cap blocks, avoiding both a (p+1)-cap and a (p+1)-strong set forces the lower child to have exactly two points in each block and be a four-cap; the upper child has 2p-4 points and cap rank exactly p-2. This is the general root mechanism behind the R24 persistent interval-normal-form obstruction; no sweep separation between the blocks is needed for the incidence conclusion.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.HasDeepBelowSplit.cap_inter_lower_card_le_two, ErdosSzekeres.HasDeepBelowSplit.containsStrongPolygonSet_of_cup_cap
@dangling-ok Required general root structure for R24 two-cap-block exact capacity and persistent noninterval obstruction; geometric endpoint lemmas connect these incidences to the later interval exclusion. -/
theorem two_full_cap_blocks_root_structure {n p : ℕ} {χ : TripleColoring n} {lower upper Z₀ Z₁ : Finset (Fin n)} (hp : 4 ≤ p) (hdeep : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty) (hupper : upper.Nonempty) (hzones : Disjoint Z₀ Z₁) (hcover : Z₀ ∪ Z₁ = lower ∪ upper) (hcap₀ : IsCapSet χ Z₀) (hcap₁ : IsCapSet χ Z₁) (hcard₀ : Z₀.card = p) (hcard₁ : Z₁.card = p) (hnoCap : ¬ ContainsCapSet χ (lower ∪ upper) (p + 1)) (hnoStrong : ¬ ContainsStrongPolygonSet χ (lower ∪ upper) (p + 1)) : (Z₀ ∩ lower).card = 2 ∧ (Z₁ ∩ lower).card = 2 ∧ lower.card = 4 ∧ IsCapSet χ lower ∧ upper.card = 2 * p - 4 ∧ ContainsCapSet χ upper (p - 2) ∧ ¬ ContainsCapSet χ upper (p - 1) := by
  classical
  have cup_small (T : Finset (Fin n)) (hT : T.card ≤ 2) : IsCupSet χ T := by
    intro t hi hj hk
    have hsub : ({t.i, t.j, t.k} : Finset (Fin n)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    have hthree : ({t.i, t.j, t.k} : Finset (Fin n)).card = 3 := by
      simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
    have := Finset.card_le_card hsub
    omega
  have cap_of_no_three (T : Finset (Fin n)) (hT : ¬ ContainsCupSet χ T 3) :
      IsCapSet χ T := by
    intro t hi hj hk
    cases hcolor : χ t with
    | right => rfl
    | left =>
      exfalso
      apply hT
      refine ⟨{t.i, t.j, t.k}, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hi
        · exact hj
        · exact hk
      · simp [ne_of_lt t.hij, ne_of_lt t.hjk, ne_of_lt (t.hij.trans t.hjk)]
      · have htij := t.hij
        have htjk := t.hjk
        rintro ⟨a, b, c, hab, hbc⟩ ha hb hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
        rcases ha with rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl <;>
            rcases hc with rfl | rfl | rfl <;> try omega
  have partition (T X Y : Finset (Fin n)) (hXY : Disjoint X Y) (hT : T ⊆ X ∪ Y) :
      T.card = (T ∩ X).card + (T ∩ Y).card := by
    have heq : T = (T ∩ X) ∪ (T ∩ Y) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hT hx) with hX | hY
        · exact Or.inl ⟨hx, hX⟩
        · exact Or.inr ⟨hx, hY⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    calc
      T.card = ((T ∩ X) ∪ (T ∩ Y)).card := congrArg Finset.card heq
      _ = (T ∩ X).card + (T ∩ Y).card :=
        Finset.card_union_of_disjoint
          (hXY.mono Finset.inter_subset_right Finset.inter_subset_right)
  have hsub₀ : Z₀ ⊆ lower ∪ upper := by
    rw [← hcover]
    exact Finset.subset_union_left
  have hsub₁ : Z₁ ⊆ lower ∪ upper := by
    rw [← hcover]
    exact Finset.subset_union_right
  have hpart₀ := partition Z₀ lower upper hdeep.disjoint hsub₀
  have hpart₁ := partition Z₁ lower upper hdeep.disjoint hsub₁
  have lower_meets (T : Finset (Fin n)) (hsub : T ⊆ lower ∪ upper)
      (hcap : IsCapSet χ T) (hcard : T.card = p) : (T ∩ lower).Nonempty := by
    by_contra hnot
    have hupperSub : T ⊆ upper := by
      intro x hx
      rcases Finset.mem_union.mp (hsub hx) with hl | hu
      · exact False.elim (hnot ⟨x, Finset.mem_inter.mpr ⟨hx, hl⟩⟩)
      · exact hu
    obtain ⟨x, hx⟩ := hlower
    exact hnoStrong (hdeep.containsStrongPolygonSet_of_cup_cap
      (cup := {x}) (cap := T) (by simpa using hx) hupperSub
      (cup_small {x} (by simp)) hcap (by simp [hcard]))
  have h₀lower := lower_meets Z₀ hsub₀ hcap₀ hcard₀
  have h₁lower := lower_meets Z₁ hsub₁ hcap₁ hcard₁
  have upper_meets (T U : Finset (Fin n)) (hdis : Disjoint T U)
      (hcoverTU : T ∪ U = lower ∪ upper) (hcapT : IsCapSet χ T)
      (hcapU : IsCapSet χ U) (hcardT : T.card = p) (hcardU : U.card = p)
      (hUlower : (U ∩ lower).Nonempty) : (T ∩ upper).Nonempty := by
    have hTsub : T ⊆ lower ∪ upper := by rw [← hcoverTU]; exact Finset.subset_union_left
    have hUsub : U ⊆ lower ∪ upper := by rw [← hcoverTU]; exact Finset.subset_union_right
    by_contra hnot
    have hTlower : T ⊆ lower := by
      intro x hx
      rcases Finset.mem_union.mp (hTsub hx) with hl | hu
      · exact hl
      · exact False.elim (hnot ⟨x, Finset.mem_inter.mpr ⟨hx, hu⟩⟩)
    obtain ⟨y, hy⟩ := hUlower
    have hyU := (Finset.mem_inter.mp hy).1
    have hyL := (Finset.mem_inter.mp hy).2
    have hynT : y ∉ T := fun hyT ↦ Finset.disjoint_left.mp hdis hyT hyU
    have hins : insert y T ⊆ lower := Finset.insert_subset hyL hTlower
    have hlarge : p + 1 ≤ lower.card := by
      have hc := Finset.card_le_card hins
      simpa [Finset.card_insert_of_notMem hynT, hcardT] using hc
    have hnotCapLower : ¬ IsCapSet χ lower := by
      intro hc
      obtain ⟨V, hVL, hVc⟩ := Finset.exists_subset_card_eq hlarge
      exact hnoCap ⟨V, hVL.trans Finset.subset_union_left, hVc,
        FinsetPolygon.IsCapSet.mono hc hVL⟩
    have hthree : ContainsCupSet χ lower 3 := by
      by_contra hn
      exact hnotCapLower (cap_of_no_three lower hn)
    have hUupper : (U ∩ upper).Nonempty := by
      obtain ⟨x, hx⟩ := hupper
      have hxTU : x ∈ T ∪ U := by rw [hcoverTU]; exact Finset.mem_union_right _ hx
      rcases Finset.mem_union.mp hxTU with hxT | hxU
      · exact False.elim (hnot ⟨x, Finset.mem_inter.mpr ⟨hxT, hx⟩⟩)
      · exact ⟨x, Finset.mem_inter.mpr ⟨hxU, hx⟩⟩
    have hUlowBound := hdeep.cap_inter_lower_card_le_two hUsub hcapU hUupper
    have hUpart := partition U lower upper hdeep.disjoint hUsub
    obtain ⟨C, hCL, hCcard, hCup⟩ := hthree
    exact hnoStrong (hdeep.containsStrongPolygonSet_of_cup_cap hCL
      (cap := U ∩ upper) Finset.inter_subset_right hCup
      (FinsetPolygon.IsCapSet.mono hcapU Finset.inter_subset_left) (by omega))
  have h₀upper := upper_meets Z₀ Z₁ hzones hcover hcap₀ hcap₁ hcard₀ hcard₁ h₁lower
  have h₁upper := upper_meets Z₁ Z₀ hzones.symm
    (by simpa [Finset.union_comm] using hcover) hcap₁ hcap₀ hcard₁ hcard₀ h₀lower
  have hbound₀ := hdeep.cap_inter_lower_card_le_two hsub₀ hcap₀ h₀upper
  have hbound₁ := hdeep.cap_inter_lower_card_le_two hsub₁ hcap₁ h₁upper
  have hLsub : lower ⊆ Z₀ ∪ Z₁ := by rw [hcover]; exact Finset.subset_union_left
  have hLpart := partition lower Z₀ Z₁ hzones hLsub
  have hLpart' : lower.card = (Z₀ ∩ lower).card + (Z₁ ∩ lower).card := by
    simpa [Finset.inter_comm] using hLpart
  have hLtwo : 2 ≤ lower.card := by
    have hpos₀ := h₀lower.card_pos
    have hpos₁ := h₁lower.card_pos
    omega
  obtain ⟨C, hCL, hCcard⟩ := Finset.exists_subset_card_eq hLtwo
  have hCup : IsCupSet χ C := cup_small C (by omega)
  have upper_cap_bound (V : Finset (Fin n)) (hV : V ⊆ upper)
      (hcap : IsCapSet χ V) : V.card + 2 ≤ p := by
    by_contra hnot
    apply hnoStrong
    exact hdeep.containsStrongPolygonSet_of_cup_cap hCL hV hCup hcap (by omega)
  have hupperBound₀ := upper_cap_bound (Z₀ ∩ upper) Finset.inter_subset_right
    (FinsetPolygon.IsCapSet.mono hcap₀ Finset.inter_subset_left)
  have hupperBound₁ := upper_cap_bound (Z₁ ∩ upper) Finset.inter_subset_right
    (FinsetPolygon.IsCapSet.mono hcap₁ Finset.inter_subset_left)
  have heq₀ : (Z₀ ∩ lower).card = 2 := by omega
  have heq₁ : (Z₁ ∩ lower).card = 2 := by omega
  have hLcard : lower.card = 4 := by omega
  have hB₀card : (Z₀ ∩ upper).card = p - 2 := by omega
  have hcapLower : IsCapSet χ lower := by
    apply cap_of_no_three
    rintro ⟨D, hDL, hDc, hCupD⟩
    exact hnoStrong (hdeep.containsStrongPolygonSet_of_cup_cap hDL
      (cap := Z₀ ∩ upper) Finset.inter_subset_right hCupD
      (FinsetPolygon.IsCapSet.mono hcap₀ Finset.inter_subset_left) (by omega))
  have htotal : (lower ∪ upper).card = 2 * p := by
    rw [← hcover, Finset.card_union_of_disjoint hzones, hcard₀, hcard₁]
    omega
  have hUcard : upper.card = 2 * p - 4 := by
    have htotal' := Finset.card_union_of_disjoint hdeep.disjoint
    omega
  refine ⟨heq₀, heq₁, hLcard, hcapLower, hUcard, ?_, ?_⟩
  · exact ⟨Z₀ ∩ upper, Finset.inter_subset_right, hB₀card,
      FinsetPolygon.IsCapSet.mono hcap₀ Finset.inter_subset_left⟩
  · rintro ⟨V, hVU, hVcard, hCapV⟩
    have := upper_cap_bound V hVU hCapV
    omega


end ErdosSzekeres
