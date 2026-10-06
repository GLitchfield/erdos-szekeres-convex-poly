import ESBlueprint.B.TwoFullCapBlocksRootStructure

namespace ErdosSzekeres

/-- Every nonempty deep-below root of two disjoint ordered full p-cap blocks, p>=4, avoiding a (p+1)-cap and a (p+1)-strong set contains a four-cup and both lower-upper-lower and upper-lower-upper sweep subsequences. The subsequences witness a gap in each root child, certifying the general forced noninterval root behind the R24 context-bound obstruction.
@node
@ws B
@kind formalization
@depends ErdosSzekeres.two_full_cap_blocks_root_structure, ErdosSzekeres.HasDeepBelowSplit.lower_mem_cap_isSweepEndpoint
@dangling-ok General geometric obstruction needed for R24 persistent interval-root failure and the cup-three gate upper; later profile and B interfaces remain separate. -/
theorem two_full_cap_blocks_root_noninterval {n p : ℕ} {χ : TripleColoring n} {lower upper Z₀ Z₁ : Finset (Fin n)} (hp : 4 ≤ p) (hdeep : HasDeepBelowSplit χ lower upper) (hlower : lower.Nonempty) (hupper : upper.Nonempty) (hzones : Disjoint Z₀ Z₁) (hcover : Z₀ ∪ Z₁ = lower ∪ upper) (hsep : ∀ x ∈ Z₀, ∀ y ∈ Z₁, x < y) (hcap₀ : IsCapSet χ Z₀) (hcap₁ : IsCapSet χ Z₁) (hcard₀ : Z₀.card = p) (hcard₁ : Z₁.card = p) (hnoCap : ¬ ContainsCapSet χ (lower ∪ upper) (p + 1)) (hnoStrong : ¬ ContainsStrongPolygonSet χ (lower ∪ upper) (p + 1)) : ContainsCupSet χ (lower ∪ upper) 4 ∧ (∃ x y z : Fin n, x ∈ lower ∧ y ∈ upper ∧ z ∈ lower ∧ x < y ∧ y < z) ∧ (∃ x y z : Fin n, x ∈ upper ∧ y ∈ lower ∧ z ∈ upper ∧ x < y ∧ y < z) := by
  classical
  obtain ⟨hcount₀, hcount₁, _, _, _, _, _⟩ :=
    two_full_cap_blocks_root_structure hp hdeep hlower hupper hzones hcover
      hcap₀ hcap₁ hcard₀ hcard₁ hnoCap hnoStrong
  have bracket (T : Finset (Fin n)) (hsub : T ⊆ lower ∪ upper)
      (hcap : IsCapSet χ T) (hcard : T.card = p) (hcount : (T ∩ lower).card = 2) :
      ∃ x y z : Fin n,
        x ∈ T ∩ lower ∧ y ∈ T ∩ upper ∧ z ∈ T ∩ lower ∧ x < y ∧ y < z := by
    have heq : (T ∩ lower) ∪ (T ∩ upper) = T := by
      ext q
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hq, _⟩ | ⟨hq, _⟩) <;> exact hq
      · intro hq
        rcases Finset.mem_union.mp (hsub hq) with hL | hU
        · exact Or.inl ⟨hq, hL⟩
        · exact Or.inr ⟨hq, hU⟩
    have hupperCard : (T ∩ upper).card = p - 2 := by
      have hc := Finset.card_union_of_disjoint
        (hdeep.disjoint.mono Finset.inter_subset_right Finset.inter_subset_right :
          Disjoint (T ∩ lower) (T ∩ upper))
      rw [heq, hcard, hcount] at hc
      omega
    have hmeet : (T ∩ upper).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y, hy⟩ := hmeet
    let e : Fin 2 ↪o Fin n := (T ∩ lower).orderEmbOfFin hcount
    let x : Fin n := e 0
    let z : Fin n := e 1
    have hx : x ∈ T ∩ lower := (T ∩ lower).orderEmbOfFin_mem hcount 0
    have hz : z ∈ T ∩ lower := (T ∩ lower).orderEmbOfFin_mem hcount 1
    have hxz : x < z := e.strictMono (by decide)
    have hendX := hdeep.lower_mem_cap_isSweepEndpoint hsub hcap ⟨y, hy⟩
      (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
    have hendZ := hdeep.lower_mem_cap_isSweepEndpoint hsub hcap ⟨y, hy⟩
      (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2
    have hleft : HasDeepBelowSplit.IsLeftSweepEndpoint T x := by
      rcases hendX with hleft | hright
      · exact hleft
      · have := hright z (Finset.mem_inter.mp hz).1
        omega
    have hright : HasDeepBelowSplit.IsRightSweepEndpoint T z := by
      rcases hendZ with hleft | hright
      · have := hleft x (Finset.mem_inter.mp hx).1
        omega
      · exact hright
    have hxy : x < y := lt_of_le_of_ne (hleft y (Finset.mem_inter.mp hy).1) (by
      intro heq
      subst y
      exact Finset.disjoint_left.mp hdeep.disjoint
        (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2)
    have hyz : y < z := lt_of_le_of_ne (hright y (Finset.mem_inter.mp hy).1) (by
      intro heq
      subst y
      exact Finset.disjoint_left.mp hdeep.disjoint
        (Finset.mem_inter.mp hz).2 (Finset.mem_inter.mp hy).2)
    exact ⟨x, y, z, hx, hy, hz, hxy, hyz⟩
  have hsub₀ : Z₀ ⊆ lower ∪ upper := by rw [← hcover]; exact Finset.subset_union_left
  have hsub₁ : Z₁ ⊆ lower ∪ upper := by rw [← hcover]; exact Finset.subset_union_right
  obtain ⟨x, a, b, hx, ha, hb, hxa, hab⟩ :=
    bracket Z₀ hsub₀ hcap₀ hcard₀ hcount₀
  obtain ⟨c, d, z, hc, hd, hz, hcd, hdz⟩ :=
    bracket Z₁ hsub₁ hcap₁ hcard₁ hcount₁
  have haU := (Finset.mem_inter.mp ha).2
  have hbL := (Finset.mem_inter.mp hb).2
  have hcL := (Finset.mem_inter.mp hc).2
  have hdU := (Finset.mem_inter.mp hd).2
  have hbc : b < c := hsep b (Finset.mem_inter.mp hb).1 c (Finset.mem_inter.mp hc).1
  have hac : a < c := hab.trans hbc
  have hbd : b < d := hbc.trans hcd
  have had : a < d := hac.trans hcd
  have haS : a ∈ lower ∪ upper := Finset.mem_union_right _ haU
  have hbS : b ∈ lower ∪ upper := Finset.mem_union_left _ hbL
  have hcS : c ∈ lower ∪ upper := Finset.mem_union_left _ hcL
  have hdS : d ∈ lower ∪ upper := Finset.mem_union_right _ hdU
  have left_mixed (t : OrderedTriple n) (hi : t.i ∈ lower ∪ upper)
      (hj : t.j ∈ lower ∪ upper) (hk : t.k ∈ lower ∪ upper)
      (hmid : t.j ∈ lower)
      (hsome : t.i ∈ upper ∨ t.j ∈ upper ∨ t.k ∈ upper) : χ t = Turn.left := by
    have hjNot : t.j ∉ upper := fun hu ↦ Finset.disjoint_left.mp hdeep.disjoint hmid hu
    have hnotL : ¬ (t.i ∈ lower ∧ t.j ∈ lower ∧ t.k ∈ lower) := by
      rintro ⟨hiL, hjL, hkL⟩
      rcases hsome with hiU | hjU | hkU
      · exact Finset.disjoint_left.mp hdeep.disjoint hiL hiU
      · exact Finset.disjoint_left.mp hdeep.disjoint hjL hjU
      · exact Finset.disjoint_left.mp hdeep.disjoint hkL hkU
    have hnotU : ¬ (t.i ∈ upper ∧ t.j ∈ upper ∧ t.k ∈ upper) := by
      rintro ⟨_, hjU, _⟩
      exact hjNot hjU
    simpa [hmid] using hdeep.crossing t hi hj hk hnotL hnotU
  have habc : χ ⟨a, b, c, hab, hbc⟩ = Turn.left :=
    left_mixed _ haS hbS hcS hbL (Or.inl haU)
  have habd : χ ⟨a, b, d, hab, hbd⟩ = Turn.left :=
    left_mixed _ haS hbS hdS hbL (Or.inl haU)
  have hacd : χ ⟨a, c, d, hac, hcd⟩ = Turn.left :=
    left_mixed _ haS hcS hdS hcL (Or.inl haU)
  have hbcd : χ ⟨b, c, d, hbc, hcd⟩ = Turn.left :=
    left_mixed _ hbS hcS hdS hcL (Or.inr (Or.inr hdU))
  have hcup : IsCupSet χ {a, b, c, d} := by
    rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
        rcases hk with rfl | rfl | rfl | rfl <;> try omega
    all_goals first | exact habc | exact habd | exact hacd | exact hbcd
  have hfour : ContainsCupSet χ (lower ∪ upper) 4 := by
    refine ⟨{a, b, c, d}, ?_, ?_, hcup⟩
    · intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact haS
      · exact hbS
      · exact hcS
      · exact hdS
    · simp [ne_of_lt hab, ne_of_lt hac, ne_of_lt had,
        ne_of_lt hbc, ne_of_lt hbd, ne_of_lt hcd]
  refine ⟨hfour, ?_, ?_⟩
  · exact ⟨x, a, b, (Finset.mem_inter.mp hx).2, haU, hbL, hxa, hab⟩
  · exact ⟨a, b, d, haU, hbL, hdU, hab, hbd⟩


end ErdosSzekeres
