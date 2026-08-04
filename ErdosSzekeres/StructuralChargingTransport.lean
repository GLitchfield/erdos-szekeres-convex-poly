module

public import ErdosSzekeres.StructuralChargingCore

@[expose] public section

/-!
# Transport and closure of the seven-vertex structural charging lemma

This file transports fixed cup, cap, and strong-polygon witnesses through
increasing restrictions, proves the reversed `4+3` normalized block theorem,
and closes `CupBlocks34Force455` for arbitrary ordered finite blocks.
-/

namespace ErdosSzekeres

theorem containsCupSet_map_restrict {m n k : ℕ} {χ : TripleColoring n}
    (f : Fin m ↪o Fin n)
    (h : ContainsCupSet (χ.restrict f) Finset.univ k) :
    ContainsCupSet χ (Finset.univ.image f) k := by
  obtain ⟨cup, _, hcard, hcup⟩ := h
  let e : Fin k ↪o Fin m := cup.orderEmbOfFin hcard
  have heCup : IsCup (χ.restrict f) e := by
    refine ⟨e.strictMono, ?_⟩
    intro i j l hij hjl
    exact hcup _ (cup.orderEmbOfFin_mem hcard i)
      (cup.orderEmbOfFin_mem hcard j) (cup.orderEmbOfFin_mem hcard l)
  let g : Fin k ↪o Fin n := e.trans f
  have hgCup : IsCup χ g := by
    exact IsMonochromaticChain.map_of_restrict_eq f rfl heCup
  refine ⟨Finset.univ.image g, ?_, ?_, FinsetPolygon.IsCup.image hgCup⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact ⟨e i, rfl⟩
  · simpa using Finset.card_image_of_injective Finset.univ g.injective

theorem containsCapSet_map_restrict {m n k : ℕ} {χ : TripleColoring n}
    (f : Fin m ↪o Fin n)
    (h : ContainsCapSet (χ.restrict f) Finset.univ k) :
    ContainsCapSet χ (Finset.univ.image f) k := by
  obtain ⟨cap, _, hcard, hcap⟩ := h
  let e : Fin k ↪o Fin m := cap.orderEmbOfFin hcard
  have heCap : IsCap (χ.restrict f) e := by
    refine ⟨e.strictMono, ?_⟩
    intro i j l hij hjl
    exact hcap _ (cap.orderEmbOfFin_mem hcard i)
      (cap.orderEmbOfFin_mem hcard j) (cap.orderEmbOfFin_mem hcard l)
  let g : Fin k ↪o Fin n := e.trans f
  have hgCap : IsCap χ g := by
    exact IsMonochromaticChain.map_of_restrict_eq f rfl heCap
  refine ⟨Finset.univ.image g, ?_, ?_, FinsetPolygon.IsCap.image hgCap⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact ⟨e i, rfl⟩
  · simpa using Finset.card_image_of_injective Finset.univ g.injective

theorem containsStrongPolygonSet_map_restrict {m n k : ℕ}
    {χ : TripleColoring n} (f : Fin m ↪o Fin n)
    (h : ContainsStrongPolygonSet (χ.restrict f) Finset.univ k) :
    ContainsStrongPolygonSet χ (Finset.univ.image f) k := by
  obtain ⟨polygon, _, hcard, hstrong⟩ := h
  let e : Fin k ↪o Fin m := polygon.orderEmbOfFin hcard
  have heStrong : IsStrongPolygonOn (χ.restrict f) e := by
    intro i j r s hij hjr hrs
    exact hstrong (e.strictMono hij) (e.strictMono hjr) (e.strictMono hrs)
      (polygon.orderEmbOfFin_mem hcard i)
      (polygon.orderEmbOfFin_mem hcard j)
      (polygon.orderEmbOfFin_mem hcard r)
      (polygon.orderEmbOfFin_mem hcard s)
  let g : Fin k ↪o Fin n := e.trans f
  have hgStrong : IsStrongPolygonOn χ g := by
    intro i j r s hij hjr hrs
    exact heStrong hij hjr hrs
  refine ⟨Finset.univ.image g, ?_, ?_,
    FinsetPolygon.IsStrongPolygonOn.isStrongPolygonSet_image hgStrong⟩
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact ⟨e i, rfl⟩
  · simpa using Finset.card_image_of_injective Finset.univ g.injective

theorem cupBlocks34Force455_three_four {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)} (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 3) (hrightCard : right.card = 4)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 5 ∨
      ContainsStrongPolygonSet χ (left ∪ right) 5 := by
  let le : Fin 3 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 4 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 7 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, re 0, re 1, re 2, re 3] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 7 := χ.restrict f
  have hfmem : ∀ i : Fin 7, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 7, i ∈ ({0, 1, 2} : Finset (Fin 7)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 7, i ∈ ({3, 4, 5, 6} : Finset (Fin 7)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {3, 4, 5, 6} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := cupBlocks34_finSeven ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 7 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard,
        himageCard]
  rcases hout with hcap | hcup | hstrong
  · left
    simpa [himage] using containsCapSet_map_restrict f hcap
  · right
    left
    simpa [himage] using containsCupSet_map_restrict f hcup
  · right
    right
    simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong

def reverseOrderedTriple {n : ℕ} (t : OrderedTriple n) : OrderedTriple n :=
  ⟨t.k.rev, t.j.rev, t.i.rev, by simpa using t.hjk, by simpa using t.hij⟩

def reverseColor {n : ℕ} (χ : TripleColoring n) : TripleColoring n :=
  fun t ↦ χ (reverseOrderedTriple t)

theorem TurnSequenceAllowed.reversed {a b c d : Turn}
    (h : TurnSequenceAllowed a b c d) : TurnSequenceAllowed d c b a := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [TurnSequenceAllowed]

private theorem rev_mem_of_mem_image_rev {n : ℕ} {s : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ s.image Fin.rev) : i.rev ∈ s := by
  simp only [Finset.mem_image] at hi
  obtain ⟨j, hj, hji⟩ := hi
  have hjrev : j = i.rev := by
    apply Fin.rev_injective
    simp [hji]
  simpa [hjrev] using hj

theorem containsCupSet_of_reverseColor {n k : ℕ} {χ : TripleColoring n}
    (h : ContainsCupSet (reverseColor χ) Finset.univ k) :
    ContainsCupSet χ Finset.univ k := by
  obtain ⟨cup, _, hcard, hcup⟩ := h
  refine ⟨cup.image Fin.rev, by simp, ?_, ?_⟩
  · exact (Finset.card_image_of_injective _ Fin.rev_injective).trans hcard
  · intro t hi hj hk
    have hri := rev_mem_of_mem_image_rev hi
    have hrj := rev_mem_of_mem_image_rev hj
    have hrk := rev_mem_of_mem_image_rev hk
    have hout := hcup (reverseOrderedTriple t) hrk hrj hri
    simpa [reverseColor, reverseOrderedTriple] using hout

theorem containsCapSet_of_reverseColor {n k : ℕ} {χ : TripleColoring n}
    (h : ContainsCapSet (reverseColor χ) Finset.univ k) :
    ContainsCapSet χ Finset.univ k := by
  obtain ⟨cap, _, hcard, hcap⟩ := h
  refine ⟨cap.image Fin.rev, by simp, ?_, ?_⟩
  · exact (Finset.card_image_of_injective _ Fin.rev_injective).trans hcard
  · intro t hi hj hk
    have hri := rev_mem_of_mem_image_rev hi
    have hrj := rev_mem_of_mem_image_rev hj
    have hrk := rev_mem_of_mem_image_rev hk
    have hout := hcap (reverseOrderedTriple t) hrk hrj hri
    simpa [reverseColor, reverseOrderedTriple] using hout

theorem containsStrongPolygonSet_of_reverseColor {n k : ℕ}
    {χ : TripleColoring n}
    (h : ContainsStrongPolygonSet (reverseColor χ) Finset.univ k) :
    ContainsStrongPolygonSet χ Finset.univ k := by
  obtain ⟨polygon, _, hcard, hstrong⟩ := h
  refine ⟨polygon.image Fin.rev, by simp, ?_, ?_⟩
  · exact (Finset.card_image_of_injective _ Fin.rev_injective).trans hcard
  · intro i j r s hij hjr hrs hi hj hr hs
    have hri := rev_mem_of_mem_image_rev hi
    have hrj := rev_mem_of_mem_image_rev hj
    have hrr := rev_mem_of_mem_image_rev hr
    have hrs' := rev_mem_of_mem_image_rev hs
    have hout := hstrong (i := s.rev) (j := r.rev) (k := j.rev) (l := i.rev)
      (by simpa using hrs) (by simpa using hjr) (by simpa using hij)
      hrs' hrr hrj hri
    simpa [reverseColor, reverseOrderedTriple] using And.intro hout.2.symm hout.1.symm

theorem cupBlocks43_finSeven
    (χ : TripleColoring 7)
    (hleft : IsCupSet χ {0, 1, 2, 3})
    (hright : IsCupSet χ {4, 5, 6})
    (hone : OneChangeOn χ Finset.univ) :
    ContainsCapSet χ Finset.univ 4 ∨
      ContainsCupSet χ Finset.univ 5 ∨
      ContainsStrongPolygonSet χ Finset.univ 5 := by
  let ψ := reverseColor χ
  have hrevFirst : ∀ i : Fin 7,
      i ∈ ({0, 1, 2} : Finset (Fin 7)) →
        i.rev ∈ ({4, 5, 6} : Finset (Fin 7)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hrevLast : ∀ i : Fin 7,
      i ∈ ({3, 4, 5, 6} : Finset (Fin 7)) →
        i.rev ∈ ({0, 1, 2, 3} : Finset (Fin 7)) := by
    intro i hi
    fin_cases i <;> simp_all
  have hψLeft : IsCupSet ψ {0, 1, 2} := by
    intro t hi hj hk
    exact hright (reverseOrderedTriple t)
      (hrevFirst t.k hk) (hrevFirst t.j hj) (hrevFirst t.i hi)
  have hψRight : IsCupSet ψ {3, 4, 5, 6} := by
    intro t hi hj hk
    exact hleft (reverseOrderedTriple t)
      (hrevLast t.k hk) (hrevLast t.j hj) (hrevLast t.i hi)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    have horig := hone (i := l.rev) (j := k.rev) (k := j.rev) (l := i.rev)
      (by simpa using hkl) (by simpa using hjk) (by simpa using hij)
      (by simp) (by simp) (by simp) (by simp)
    simpa [ψ, reverseColor, reverseOrderedTriple] using horig.reversed
  rcases cupBlocks34_finSeven ψ hψLeft hψRight hψOne with hcap | hcup | hstrong
  · exact Or.inl (containsCapSet_of_reverseColor hcap)
  · exact Or.inr (Or.inl (containsCupSet_of_reverseColor hcup))
  · exact Or.inr (Or.inr (containsStrongPolygonSet_of_reverseColor hstrong))

theorem cupBlocks34Force455_four_three {n : ℕ} {χ : TripleColoring n}
    {left right : Finset (Fin n)} (hdisjoint : Disjoint left right)
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hleftCard : left.card = 4) (hrightCard : right.card = 3)
    (hleft : IsCupSet χ left) (hright : IsCupSet χ right)
    (hone : OneChangeOn χ (left ∪ right)) :
    ContainsCapSet χ (left ∪ right) 4 ∨
      ContainsCupSet χ (left ∪ right) 5 ∨
      ContainsStrongPolygonSet χ (left ∪ right) 5 := by
  let le : Fin 4 ↪o Fin n := left.orderEmbOfFin hleftCard
  let re : Fin 3 ↪o Fin n := right.orderEmbOfFin hrightCard
  let f : Fin 7 ↪o Fin n := OrderEmbedding.ofStrictMono
    ![le 0, le 1, le 2, le 3, re 0, re 1, re 2] (by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals (try norm_num at hij)
      all_goals first
        | exact le.strictMono (by decide)
        | exact re.strictMono (by decide)
        | exact horder _ (left.orderEmbOfFin_mem hleftCard _)
            _ (right.orderEmbOfFin_mem hrightCard _))
  let ψ : TripleColoring 7 := χ.restrict f
  have hfmem : ∀ i : Fin 7, f i ∈ left ∪ right := by
    intro i
    fin_cases i <;>
      simp [f, le, re, left.orderEmbOfFin_mem hleftCard,
        right.orderEmbOfFin_mem hrightCard]
  have hfirst : ∀ i : Fin 7, i ∈ ({0, 1, 2, 3} : Finset (Fin 7)) → f i ∈ left := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      exact left.orderEmbOfFin_mem hleftCard _
  have hlast : ∀ i : Fin 7, i ∈ ({4, 5, 6} : Finset (Fin 7)) → f i ∈ right := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact right.orderEmbOfFin_mem hrightCard _
  have hψLeft : IsCupSet ψ {0, 1, 2, 3} := by
    intro t hi hj hk
    exact hleft (t.map f) (hfirst t.i hi) (hfirst t.j hj) (hfirst t.k hk)
  have hψRight : IsCupSet ψ {4, 5, 6} := by
    intro t hi hj hk
    exact hright (t.map f) (hlast t.i hi) (hlast t.j hj) (hlast t.k hk)
  have hψOne : OneChangeOn ψ Finset.univ := by
    intro i j k l hij hjk hkl _ _ _ _
    exact hone (f.strictMono hij) (f.strictMono hjk) (f.strictMono hkl)
      (hfmem i) (hfmem j) (hfmem k) (hfmem l)
  have hout := cupBlocks43_finSeven ψ hψLeft hψRight hψOne
  have himage : Finset.univ.image f = left ∪ right := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hfmem i
    · have himageCard : (Finset.univ.image f).card = 7 := by
        simpa using Finset.card_image_of_injective Finset.univ f.injective
      rw [Finset.card_union_of_disjoint hdisjoint, hleftCard, hrightCard,
        himageCard]
  rcases hout with hcap | hcup | hstrong
  · left
    simpa [himage] using containsCapSet_map_restrict f hcap
  · right
    left
    simpa [himage] using containsCupSet_map_restrict f hcup
  · right
    right
    simpa [himage] using containsStrongPolygonSet_map_restrict f hstrong

theorem cupBlocks34Force455 : CupBlocks34Force455 := by
  intro n χ left right hdisjoint horder hcards hleft hright hone
  rcases hcards with ⟨hleftCard, hrightCard⟩ | ⟨hleftCard, hrightCard⟩
  · exact cupBlocks34Force455_three_four hdisjoint horder hleftCard hrightCard
      hleft hright hone
  · exact cupBlocks34Force455_four_three hdisjoint horder hleftCard hrightCard
      hleft hright hone

theorem upperChildGapTrichotomyAtSeven : UpperChildGapTrichotomyAtSeven :=
  upperChildGapTrichotomyAtSeven_of_cupBlocks34 cupBlocks34Force455

theorem HasDeepBelowSplit.singleton_root_card_le_seven {n : ℕ}
    {χ : TripleColoring n} {upper : Finset (Fin n)} {q : Fin n}
    (hupper : IsDecomposableOn χ upper)
    (h : HasDeepBelowSplit χ {q} upper)
    (hnoCap : ¬ContainsCapSet χ ({q} ∪ upper) 4)
    (hnoCup : ¬ContainsCupSet χ ({q} ∪ upper) 5)
    (hnoStrong : ¬ContainsStrongPolygonSet χ ({q} ∪ upper) 5) :
    ({q} ∪ upper).card ≤ 7 :=
  HasDeepBelowSplit.singleton_root_card_le_seven_of_gapTrichotomy
    upperChildGapTrichotomyAtSeven hupper h hnoCap hnoCup hnoStrong

end ErdosSzekeres
