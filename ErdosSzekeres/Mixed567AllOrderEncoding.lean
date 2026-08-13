module

public import ErdosSzekeres.Mixed567AllOrderStructural

@[expose] public section

/-!
# Semantic interface for the mixed state-567 encoding-A certificate

The SAT variables for an unordered triple are interpreted by sorting its
embedded image.  Thus their meaning is independent of the arbitrary order in
which the twelve labels occur in the ambient sweep.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace ErdosSzekeres

noncomputable section

private def mixed567TripleEmbedding {n : ℕ} (i j k : Fin n)
    (hij : i < j) (hjk : j < k) : Fin 3 ↪o Fin n :=
  OrderEmbedding.ofStrictMono ![i, j, k] (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;> omega)

private theorem image_mixed567TripleEmbedding {n : ℕ} (i j k : Fin n)
    (hij : i < j) (hjk : j < k) :
    Finset.univ.image (mixed567TripleEmbedding i j k hij hjk) = {i, j, k} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp [mixed567TripleEmbedding]
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp [mixed567TripleEmbedding]⟩
    · exact ⟨1, by simp [mixed567TripleEmbedding]⟩
    · exact ⟨2, by simp [mixed567TripleEmbedding]⟩

/-- Interpretation of one unordered-triple color variable of encoding A. -/
def Mixed567ColorAtom {n : ℕ} (χ : TripleColoring n) (embed : Fin 12 ↪ Fin n)
    (support : Finset (Fin 12)) (hcard : support.card = 3) : Prop :=
  let image := support.image embed
  let himage : image.card = 3 := by
    simpa [image, Finset.card_image_of_injective _ embed.injective] using hcard
  let f : Fin 3 ↪o Fin n := image.orderEmbOfFin himage
  χ ⟨f 0, f 1, f 2, f.strictMono (by decide), f.strictMono (by decide)⟩ = Turn.left

theorem mixed567ColorAtom_eq_of_order {n : ℕ} (χ : TripleColoring n)
    (embed : Fin 12 ↪ Fin n) (support : Finset (Fin 12))
    (hcard : support.card = 3) (a b c : Fin 12)
    (hsupport : support = {a, b, c})
    (hab : embed a < embed b) (hbc : embed b < embed c) :
    Mixed567ColorAtom χ embed support hcard ↔
      χ ⟨embed a, embed b, embed c, hab, hbc⟩ = Turn.left := by
  let image := support.image embed
  have himage : image.card = 3 := by
    simpa [image, Finset.card_image_of_injective _ embed.injective] using hcard
  let f := mixed567TripleEmbedding (embed a) (embed b) (embed c) hab hbc
  have hfimage : Finset.univ.image f = image := by
    rw [image_mixed567TripleEmbedding]
    simp [image, hsupport]
  have hfeq : f = image.orderEmbOfFin himage :=
    Finset.orderEmbOfFin_unique' himage (by
      intro x
      rw [← hfimage]
      exact Finset.mem_image_of_mem f (Finset.mem_univ x))
  unfold Mixed567ColorAtom
  dsimp only
  have h0 : image.orderEmbOfFin himage 0 = embed a := by
    rw [← hfeq]
    simp [f, mixed567TripleEmbedding]
  have h1 : image.orderEmbOfFin himage 1 = embed b := by
    rw [← hfeq]
    simp [f, mixed567TripleEmbedding]
  have h2 : image.orderEmbOfFin himage 2 = embed c := by
    rw [← hfeq]
    simp [f, mixed567TripleEmbedding]
  have htriple :
      (⟨image.orderEmbOfFin himage 0, image.orderEmbOfFin himage 1,
          image.orderEmbOfFin himage 2,
          (image.orderEmbOfFin himage).strictMono (by decide),
          (image.orderEmbOfFin himage).strictMono (by decide)⟩ : OrderedTriple n) =
        ⟨embed a, embed b, embed c, hab, hbc⟩ := by
    rw [OrderedTriple.mk.injEq]
    exact ⟨h0, h1, h2⟩
  rw [htriple]

/-- Interpretation of an exactly reified strong-four variable of encoding A. -/
def Mixed567StrongAtom {n : ℕ} (χ : TripleColoring n) (embed : Fin 12 ↪ Fin n)
    (support : Finset (Fin 12)) : Prop :=
  IsStrongPolygonSet χ (support.image embed)

theorem mixed567StrongAtom_mono {n : ℕ} {χ : TripleColoring n}
    {embed : Fin 12 ↪ Fin n} {small large : Finset (Fin 12)}
    (hlarge : Mixed567StrongAtom χ embed large) (hsub : small ⊆ large) :
    Mixed567StrongAtom χ embed small := by
  exact FinsetPolygon.IsStrongPolygonSet.mono hlarge
    (Finset.image_mono embed hsub)

theorem mixed567StrongAtom_iff_of_order {n : ℕ} (χ : TripleColoring n)
    (embed : Fin 12 ↪ Fin n) (support : Finset (Fin 12))
    (a b c d : Fin 12) (hsupport : support = {a, b, c, d})
    (hab : embed a < embed b) (hbc : embed b < embed c)
    (hcd : embed c < embed d) :
    Mixed567StrongAtom χ embed support ↔
      χ ⟨embed a, embed b, embed c, hab, hbc⟩ =
          χ ⟨embed a, embed b, embed d, hab, hbc.trans hcd⟩ ∧
        χ ⟨embed a, embed c, embed d, hab.trans hbc, hcd⟩ =
          χ ⟨embed b, embed c, embed d, hbc, hcd⟩ := by
  have himage : support.image embed =
      {embed a, embed b, embed c, embed d} := by
    ext x
    simp [hsupport]
  rw [Mixed567StrongAtom, himage]
  constructor
  · intro hstrong
    exact hstrong hab hbc hcd (by simp) (by simp) (by simp) (by simp)
  · rintro ⟨hleft, hright⟩ i j k l hij hjk hkl hi hj hk hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk hl
    rcases hi with rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl | rfl <;>
      rcases hl with rfl | rfl | rfl | rfl <;> try omega
    exact ⟨hleft, hright⟩

theorem isTurnPolygonSet_image_of_colorAtoms {n cardinality : ℕ}
    (χ : TripleColoring n) (embed : Fin 12 ↪ Fin n)
    (support : Finset (Fin 12)) (hcard : support.card = cardinality)
    (turn : Turn)
    (hall : ∀ triple (htriple : triple ∈ support.powersetCard 3),
      if turn = Turn.left then
        Mixed567ColorAtom χ embed triple (Finset.mem_powersetCard.mp htriple).2
      else
        ¬Mixed567ColorAtom χ embed triple (Finset.mem_powersetCard.mp htriple).2) :
    IsTurnPolygonSet χ (support.image embed) turn := by
  intro i j k hij hjk hi hj hk
  simp only [Finset.mem_image] at hi hj hk
  obtain ⟨a, ha, rfl⟩ := hi
  obtain ⟨b, hb, rfl⟩ := hj
  obtain ⟨c, hc, rfl⟩ := hk
  have hab : a ≠ b := fun h ↦ (ne_of_lt hij) (congrArg embed h)
  have hbc : b ≠ c := fun h ↦ (ne_of_lt hjk) (congrArg embed h)
  have hac : a ≠ c := fun h ↦ (ne_of_lt (hij.trans hjk)) (congrArg embed h)
  have htripleCard : ({a, b, c} : Finset (Fin 12)).card = 3 := by
    simp [hab, hbc, hac]
  have htripleMem : ({a, b, c} : Finset (Fin 12)) ∈ support.powersetCard 3 := by
    rw [Finset.mem_powersetCard]
    refine ⟨?_, htripleCard⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hatom := hall {a, b, c} htripleMem
  have heq := mixed567ColorAtom_eq_of_order χ embed {a, b, c} htripleCard
    a b c rfl hij hjk
  by_cases hturn : turn = Turn.left
  · subst turn
    exact heq.mp (by simpa using hatom)
  · have hnotAtom :
        ¬Mixed567ColorAtom χ embed {a, b, c} htripleCard := by
      simpa [hturn] using hatom
    have hnotLeft : ¬(χ ⟨embed a, embed b, embed c, hij, hjk⟩ = Turn.left) := by
      intro hleft
      exact hnotAtom (heq.mpr hleft)
    cases hcolor : χ ⟨embed a, embed b, embed c, hij, hjk⟩
    · exact (hnotLeft hcolor).elim
    · cases turn <;> simp_all

theorem isStrongPolygonSet_image_of_strongAtoms {n : ℕ}
    (χ : TripleColoring n) (embed : Fin 12 ↪ Fin n)
    (support : Finset (Fin 12))
    (hall : ∀ four ∈ support.powersetCard 4, Mixed567StrongAtom χ embed four) :
    IsStrongPolygonSet χ (support.image embed) := by
  intro i j k l hij hjk hkl hi hj hk hl
  simp only [Finset.mem_image] at hi hj hk hl
  obtain ⟨a, ha, rfl⟩ := hi
  obtain ⟨b, hb, rfl⟩ := hj
  obtain ⟨c, hc, rfl⟩ := hk
  obtain ⟨d, hd, rfl⟩ := hl
  have hab : a ≠ b := fun h ↦ (ne_of_lt hij) (congrArg embed h)
  have hac : a ≠ c := fun h ↦ (ne_of_lt (hij.trans hjk)) (congrArg embed h)
  have had : a ≠ d := fun h ↦
    (ne_of_lt (hij.trans (hjk.trans hkl))) (congrArg embed h)
  have hbc : b ≠ c := fun h ↦ (ne_of_lt hjk) (congrArg embed h)
  have hbd : b ≠ d := fun h ↦ (ne_of_lt (hjk.trans hkl)) (congrArg embed h)
  have hcd : c ≠ d := fun h ↦ (ne_of_lt hkl) (congrArg embed h)
  have hfourCard : ({a, b, c, d} : Finset (Fin 12)).card = 4 := by
    simp [hab, hac, had, hbc, hbd, hcd]
  have hfourMem : ({a, b, c, d} : Finset (Fin 12)) ∈ support.powersetCard 4 := by
    rw [Finset.mem_powersetCard]
    refine ⟨?_, hfourCard⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  exact hall {a, b, c, d} hfourMem hij hjk hkl (by simp) (by simp) (by simp) (by simp)

end

end ErdosSzekeres

end
