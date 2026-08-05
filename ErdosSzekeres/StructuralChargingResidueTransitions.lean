module

public import ErdosSzekeres.StructuralChargingWitnessBranches

@[expose] public section

/-!
# Balanced residue transition laws

The balanced structural-charging branch represents every through-cap by a
three-vertex residue and every through-strong-six by a five-vertex residue.
This file records the first coupling laws for two external vertices sharing
one residue.
-/

namespace ErdosSzekeres

/-- Among three five-subsets of an eleven-set, two share at least two
vertices. This is the first choice-independent incidence coupling available
for distinct strong residues. -/
theorem three_five_subsets_of_eleven_pair_overlap
    {n : ℕ} {side a b c : Finset (Fin n)}
    (hsideCard : side.card = 11) (haSub : a ⊆ side)
    (hbSub : b ⊆ side) (hcSub : c ⊆ side)
    (haCard : a.card = 5) (hbCard : b.card = 5) (hcCard : c.card = 5) :
    2 ≤ (a ∩ b).card ∨ 2 ≤ (a ∩ c).card ∨ 2 ≤ (b ∩ c).card := by
  by_contra h
  push Not at h
  have habLe : (a ∩ b).card ≤ 1 := by omega
  have hacLe : (a ∩ c).card ≤ 1 := by omega
  have hbcLe : (b ∩ c).card ≤ 1 := by omega
  have habUnion : 9 ≤ (a ∪ b).card := by
    have hcard := Finset.card_union_add_card_inter a b
    omega
  have hinterSub : (a ∪ b) ∩ c ⊆ (a ∩ c) ∪ (b ∩ c) := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hab, hc⟩
    rcases Finset.mem_union.mp hab with ha | hb
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hb, hc⟩)
  have hinterCard : ((a ∪ b) ∩ c).card ≤ 2 := by
    calc
      ((a ∪ b) ∩ c).card ≤ ((a ∩ c) ∪ (b ∩ c)).card :=
        Finset.card_le_card hinterSub
      _ ≤ (a ∩ c).card + (b ∩ c).card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have habcUnion : 12 ≤ ((a ∪ b) ∪ c).card := by
    have hcard := Finset.card_union_add_card_inter (a ∪ b) c
    omega
  have habcSub : (a ∪ b) ∪ c ⊆ side :=
    Finset.union_subset (Finset.union_subset haSub hbSub) hcSub
  have := Finset.card_le_card habcSub
  omega

/-- The colors through an ordered external pair can only move toward `right`
as the third vertex advances through the base. -/
def IsRightMonotonePairProfile {n : ℕ} (χ : TripleColoring n)
    (base : Finset (Fin n)) (q r : Fin n) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) : Prop :=
  ∀ ⦃x y : Fin n⦄, (hx : x ∈ base) → (hy : y ∈ base) → x < y →
    χ ⟨q, r, x, hqr, hafter x hx⟩ = Turn.right →
      χ ⟨q, r, y, hqr, hafter y hy⟩ = Turn.right

/-- Mirror orientation: when the base precedes the external pair, colors can
only move toward `left` as the base vertex advances. -/
def IsLeftMonotonePairProfileBefore {n : ℕ} (χ : TripleColoring n)
    (base : Finset (Fin n)) (q r : Fin n) (hqr : q < r)
    (hbefore : ∀ x ∈ base, x < q) : Prop :=
  ∀ ⦃x y : Fin n⦄, (hx : x ∈ base) → (hy : y ∈ base) → x < y →
    χ ⟨x, q, r, hbefore x hx, hqr⟩ = Turn.left →
      χ ⟨y, q, r, hbefore y hy, hqr⟩ = Turn.left

/-- Two external vertices which form caps with the same residue have a
right-monotone pair profile across that residue. -/
theorem sharedCapResidue_pairProfile_rightMonotone
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n} (hqr : q < r) (hafter : ∀ x ∈ base, r < x)
    (hbaseSub : base ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hrAmbient : r ∈ ambient) (hone : OneChangeOn χ ambient)
    (hqCap : IsCapSet χ (insert q base))
    (hrCap : IsCapSet χ (insert r base)) :
    IsRightMonotonePairProfile χ base q r hqr hafter := by
  intro x y hx hy hxy hxRight
  have hqx : q < x := hqr.trans (hafter x hx)
  have hqy : q < y := hqx.trans hxy
  have hry : r < y := (hafter x hx).trans hxy
  have hqxy : χ ⟨q, x, y, hqx, hxy⟩ = Turn.right :=
    hqCap _ (Finset.mem_insert_self q base)
      (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
  have hrxy : χ ⟨r, x, y, hafter x hx, hxy⟩ = Turn.right :=
    hrCap _ (Finset.mem_insert_self r base)
      (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
  have hallowed := hone hqr (hafter x hx) hxy hqAmbient hrAmbient
    (hbaseSub hx) (hbaseSub hy)
  cases hyColor : χ ⟨q, r, y, hqr, hry⟩ <;>
    simp_all [TurnSequenceAllowed]

/-- Mirror shared-cap transition for a common residue preceding both external
vertices. -/
theorem sharedCapResidue_pairProfile_leftMonotone_before
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n} (hqr : q < r) (hbefore : ∀ x ∈ base, x < q)
    (hbaseSub : base ⊆ ambient) (hqAmbient : q ∈ ambient)
    (hrAmbient : r ∈ ambient) (hone : OneChangeOn χ ambient)
    (hqCap : IsCapSet χ (insert q base))
    (hrCap : IsCapSet χ (insert r base)) :
    IsLeftMonotonePairProfileBefore χ base q r hqr hbefore := by
  intro x y hx hy hxy hxLeft
  have hxq := hbefore x hx
  have hyq := hbefore y hy
  have hxr := hxq.trans hqr
  have hyr := hyq.trans hqr
  have hxyq : χ ⟨x, y, q, hxy, hyq⟩ = Turn.right :=
    hqCap _ (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
      (Finset.mem_insert_self q base)
  have hxyr : χ ⟨x, y, r, hxy, hyr⟩ = Turn.right :=
    hrCap _ (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
      (Finset.mem_insert_self r base)
  have hallowed := hone hxy hyq hqr (hbaseSub hx) (hbaseSub hy)
    hqAmbient hrAmbient
  cases hyColor : χ ⟨y, q, r, hyq, hqr⟩ <;>
    simp_all [TurnSequenceAllowed]

/-- On a three-vertex residue, right monotonicity leaves exactly the four
threshold words `LLL`, `LLR`, `LRR`, and `RRR`. -/
theorem rightMonotonePairProfile_three_signature
    {n : ℕ} {χ : TripleColoring n} {base : Finset (Fin n)}
    {q r : Fin n} (hcard : base.card = 3) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x)
    (hprofile : IsRightMonotonePairProfile χ base q r hqr hafter) :
    let e := base.orderEmbOfFin hcard
    (χ ⟨q, r, e 0, hqr, hafter _ (base.orderEmbOfFin_mem hcard 0)⟩ =
        Turn.left ∧
      χ ⟨q, r, e 1, hqr, hafter _ (base.orderEmbOfFin_mem hcard 1)⟩ =
        Turn.left ∧
      χ ⟨q, r, e 2, hqr, hafter _ (base.orderEmbOfFin_mem hcard 2)⟩ =
        Turn.left) ∨
    (χ ⟨q, r, e 0, hqr, hafter _ (base.orderEmbOfFin_mem hcard 0)⟩ =
        Turn.left ∧
      χ ⟨q, r, e 1, hqr, hafter _ (base.orderEmbOfFin_mem hcard 1)⟩ =
        Turn.left ∧
      χ ⟨q, r, e 2, hqr, hafter _ (base.orderEmbOfFin_mem hcard 2)⟩ =
        Turn.right) ∨
    (χ ⟨q, r, e 0, hqr, hafter _ (base.orderEmbOfFin_mem hcard 0)⟩ =
        Turn.left ∧
      χ ⟨q, r, e 1, hqr, hafter _ (base.orderEmbOfFin_mem hcard 1)⟩ =
        Turn.right ∧
      χ ⟨q, r, e 2, hqr, hafter _ (base.orderEmbOfFin_mem hcard 2)⟩ =
        Turn.right) ∨
    (χ ⟨q, r, e 0, hqr, hafter _ (base.orderEmbOfFin_mem hcard 0)⟩ =
        Turn.right ∧
      χ ⟨q, r, e 1, hqr, hafter _ (base.orderEmbOfFin_mem hcard 1)⟩ =
        Turn.right ∧
      χ ⟨q, r, e 2, hqr, hafter _ (base.orderEmbOfFin_mem hcard 2)⟩ =
        Turn.right) := by
  dsimp only
  let e : Fin 3 ↪o Fin n := base.orderEmbOfFin hcard
  have heMem (i : Fin 3) : e i ∈ base := base.orderEmbOfFin_mem hcard i
  have h01 := hprofile (heMem 0) (heMem 1) (e.strictMono (by decide))
  have h12 := hprofile (heMem 1) (heMem 2) (e.strictMono (by decide))
  generalize hc0 : χ ⟨q, r, e 0, hqr, hafter _ (heMem 0)⟩ = c0 at *
  generalize hc1 : χ ⟨q, r, e 1, hqr, hafter _ (heMem 1)⟩ = c1 at *
  generalize hc2 : χ ⟨q, r, e 2, hqr, hafter _ (heMem 2)⟩ = c2 at *
  cases c0 <;> cases c1 <;> cases c2 <;> simp_all

/-- If the external-pair profile is entirely right, two cap extensions over
the same base glue to a larger cap. -/
theorem sharedCapResidue_glue
    {n : ℕ} {χ : TripleColoring n} {base : Finset (Fin n)}
    {q r : Fin n} (hqr : q < r) (hafter : ∀ x ∈ base, r < x)
    (hqCap : IsCapSet χ (insert q base))
    (hrCap : IsCapSet χ (insert r base))
    (hpair : ∀ x, (hx : x ∈ base) →
      χ ⟨q, r, x, hqr, hafter x hx⟩ = Turn.right) :
    IsCapSet χ (insert q (insert r base)) := by
  have memInsertROfAfterQ {x : Fin n} (hx : x ∈ insert q (insert r base))
      (hqx : q < x) : x ∈ insert r base := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (lt_irrefl _ hqx).elim
    · exact hx
  have memBaseOfAfterR {x : Fin n} (hx : x ∈ insert q (insert r base))
      (hrx : r < x) : x ∈ base := by
    have hxInsertR := memInsertROfAfterQ hx (hqr.trans hrx)
    rcases Finset.mem_insert.mp hxInsertR with rfl | hxBase
    · exact (lt_irrefl _ hrx).elim
    · exact hxBase
  rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
  by_cases hiq : i = q
  · subst i
    have hjInsertR := memInsertROfAfterQ hj hij
    by_cases hjr : j = r
    · subst j
      exact hpair k (memBaseOfAfterR hk hjk)
    · have hjBase : j ∈ base :=
        (Finset.mem_insert.mp hjInsertR).resolve_left hjr
      have hkBase := memBaseOfAfterR hk ((hafter j hjBase).trans hjk)
      exact hqCap _ (Finset.mem_insert_self q base)
        (Finset.mem_insert_of_mem hjBase) (Finset.mem_insert_of_mem hkBase)
  · have hiInsertR : i ∈ insert r base :=
      (Finset.mem_insert.mp hi).resolve_left hiq
    have hqi : q < i := by
      rcases Finset.mem_insert.mp hiInsertR with rfl | hiBase
      · exact hqr
      · exact hqr.trans (hafter i hiBase)
    exact hrCap _ hiInsertR
      (memInsertROfAfterQ hj (hqi.trans hij))
      (memInsertROfAfterQ hk (hqi.trans (hij.trans hjk)))

/-- In the no-cap-five branch, a shared cap-three residue cannot have the
all-right pair profile. -/
theorem sharedCapThreeResidue_not_allRight
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n} (hcard : base.card = 3) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) (hbaseSub : base ⊆ ambient)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hqCap : IsCapSet χ (insert q base))
    (hrCap : IsCapSet χ (insert r base))
    (hnoCap : ¬ContainsCapSet χ ambient 5) :
    ¬∀ x, (hx : x ∈ base) →
      χ ⟨q, r, x, hqr, hafter x hx⟩ = Turn.right := by
  intro hpair
  have hqBase : q ∉ base := by
    intro hqBase
    exact (not_lt_of_ge hqr.le) (hafter q hqBase)
  have hrBase : r ∉ base := by
    intro hrBase
    exact (lt_irrefl r) (hafter r hrBase)
  have hqInsert : q ∉ insert r base := by simp [hqBase, hqr.ne]
  apply hnoCap
  refine ⟨insert q (insert r base), ?_, ?_,
    sharedCapResidue_glue hqr hafter hqCap hrCap hpair⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hqAmbient
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hrAmbient
      · exact hbaseSub hx
  · simp [Finset.card_insert_of_notMem, hqInsert, hrBase, hcard]

/-- If two extension colors across a quadruple disagree, the external pair
colors are forced to agree with the earlier extension color. -/
theorem sharedStrongResidue_disagreement_forces_pairColors
    {n : ℕ} {χ : TripleColoring n} {ambient : Finset (Fin n)}
    {q r x y : Fin n} (hqr : q < r) (hrx : r < x) (hxy : x < y)
    (hq : q ∈ ambient) (hr : r ∈ ambient)
    (hx : x ∈ ambient) (hy : y ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hdiff : χ ⟨q, x, y, hqr.trans hrx, hxy⟩ ≠
      χ ⟨r, x, y, hrx, hxy⟩) :
    χ ⟨q, r, x, hqr, hrx⟩ =
        χ ⟨q, r, y, hqr, hrx.trans hxy⟩ ∧
      χ ⟨q, r, y, hqr, hrx.trans hxy⟩ =
        χ ⟨q, x, y, hqr.trans hrx, hxy⟩ := by
  exact (hone hqr hrx hxy hq hr hx hy).head_eq_of_third_ne_fourth hdiff

/-- Shared strong residues agree on every extension color whose middle has an
earlier vertex in the common base. Thus extension disagreement is confined to
the first base middle. -/
theorem sharedStrongResidue_laterMiddle_extensionColors_eq
    {n : ℕ} {χ : TripleColoring n} {base : Finset (Fin n)}
    {q r a x y : Fin n} (hqr : q < r) (hra : r < a)
    (hax : a < x) (hxy : x < y) (ha : a ∈ base)
    (hx : x ∈ base) (hy : y ∈ base)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base)) :
    χ ⟨q, x, y, hqr.trans (hra.trans hax), hxy⟩ =
      χ ⟨r, x, y, hra.trans hax, hxy⟩ := by
  have hqMiddle : IsMiddleDeterminedOn χ (insert q base) :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hqStrong
  have hrMiddle : IsMiddleDeterminedOn χ (insert r base) :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hrStrong
  have hqEq := hqMiddle (hqr.trans (hra.trans hax)) hax hxy hxy
    (Finset.mem_insert_self q base) (Finset.mem_insert_of_mem ha)
    (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
    (Finset.mem_insert_of_mem hy)
  have hrEq := hrMiddle (hra.trans hax) hax hxy hxy
    (Finset.mem_insert_self r base) (Finset.mem_insert_of_mem ha)
    (Finset.mem_insert_of_mem hx) (Finset.mem_insert_of_mem hy)
    (Finset.mem_insert_of_mem hy)
  exact hqEq.trans hrEq.symm

/-- The colors through the ordered external pair are constant across the
common base. -/
def IsConstantPairProfile {n : ℕ} (χ : TripleColoring n)
    (base : Finset (Fin n)) (q r : Fin n) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) : Prop :=
  ∀ x, (hx : x ∈ base) → ∀ y, (hy : y ∈ base) →
    χ ⟨q, r, x, hqr, hafter x hx⟩ =
      χ ⟨q, r, y, hqr, hafter y hy⟩

/-- The two strong extensions give the same color whenever their common base
supplies the middle and final vertices. -/
def SharedExtensionColorsAgree {n : ℕ} (χ : TripleColoring n)
    (base : Finset (Fin n)) (q r : Fin n) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) : Prop :=
  ∀ x, (hx : x ∈ base) → ∀ y, (hy : y ∈ base) → (hxy : x < y) →
    χ ⟨q, x, y, hqr.trans (hafter x hx), hxy⟩ =
      χ ⟨r, x, y, hafter x hx, hxy⟩

/-- Two strong extensions over a common base glue to one larger strong set
exactly when their external-pair profile is constant and their base-middle
extension colors agree. -/
theorem sharedStrongResidue_glue
    {n : ℕ} {χ : TripleColoring n} {base : Finset (Fin n)}
    {q r : Fin n} (hqr : q < r) (hafter : ∀ x ∈ base, r < x)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hpair : IsConstantPairProfile χ base q r hqr hafter)
    (hext : SharedExtensionColorsAgree χ base q r hqr hafter) :
    IsStrongPolygonSet χ (insert q (insert r base)) := by
  have memInsertROfAfterQ {x : Fin n} (hx : x ∈ insert q (insert r base))
      (hqx : q < x) : x ∈ insert r base := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (lt_irrefl _ hqx).elim
    · exact hx
  have memBaseOfAfterR {x : Fin n} (hx : x ∈ insert q (insert r base))
      (hrx : r < x) : x ∈ base := by
    have hxInsertR := memInsertROfAfterQ hx (hqr.trans hrx)
    rcases Finset.mem_insert.mp hxInsertR with rfl | hxBase
    · exact (lt_irrefl _ hrx).elim
    · exact hxBase
  intro i j k l hij hjk hkl hi hj hk hl
  by_cases hiq : i = q
  · subst i
    have hjInsertR := memInsertROfAfterQ hj hij
    by_cases hjr : j = r
    · subst j
      have hkBase := memBaseOfAfterR hk hjk
      have hlBase := memBaseOfAfterR hl (hjk.trans hkl)
      exact ⟨hpair k hkBase l hlBase, hext k hkBase l hlBase hkl⟩
    · have hjBase : j ∈ base :=
        (Finset.mem_insert.mp hjInsertR).resolve_left hjr
      have hrj := hafter j hjBase
      have hkBase := memBaseOfAfterR hk (hrj.trans hjk)
      have hlBase := memBaseOfAfterR hl (hrj.trans (hjk.trans hkl))
      exact hqStrong hij hjk hkl (Finset.mem_insert_self q base)
        (Finset.mem_insert_of_mem hjBase) (Finset.mem_insert_of_mem hkBase)
        (Finset.mem_insert_of_mem hlBase)
  · have hiInsertR : i ∈ insert r base :=
      (Finset.mem_insert.mp hi).resolve_left hiq
    have hqi : q < i := by
      rcases Finset.mem_insert.mp hiInsertR with rfl | hiBase
      · exact hqr
      · exact hqr.trans (hafter i hiBase)
    have hjInsertR := memInsertROfAfterQ hj (hqi.trans hij)
    have hkInsertR := memInsertROfAfterQ hk (hqi.trans (hij.trans hjk))
    have hlInsertR := memInsertROfAfterQ hl
      (hqi.trans (hij.trans (hjk.trans hkl)))
    exact hrStrong hij hjk hkl hiInsertR hjInsertR hkInsertR hlInsertR

/-- In the no-strong-seven branch, two vertices sharing one strong-five
residue must fail one of the two exact gluing conditions. -/
theorem sharedStrongFiveResidue_pairVariation_or_extensionDisagreement
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n} (hcard : base.card = 5) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) (hbaseSub : base ⊆ ambient)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 7) :
    ¬IsConstantPairProfile χ base q r hqr hafter ∨
      ¬SharedExtensionColorsAgree χ base q r hqr hafter := by
  by_cases hpair : IsConstantPairProfile χ base q r hqr hafter
  · apply Or.inr
    intro hext
    have hqBase : q ∉ base := by
      intro hqBase
      exact (not_lt_of_ge hqr.le) (hafter q hqBase)
    have hrBase : r ∉ base := by
      intro hrBase
      exact (lt_irrefl r) (hafter r hrBase)
    have hqInsert : q ∉ insert r base := by simp [hqBase, hqr.ne]
    apply hnoStrong
    refine ⟨insert q (insert r base), ?_, ?_,
      sharedStrongResidue_glue hqr hafter hqStrong hrStrong hpair hext⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hqAmbient
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hrAmbient
        · exact hbaseSub hx
    · simp [Finset.card_insert_of_notMem, hqInsert, hrBase, hcard]
  · exact Or.inl hpair

/-- The only base middle at which two strong extensions can disagree is the
first vertex of their common five-residue. -/
def HasFirstMiddleExtensionDisagreement {n : ℕ} (χ : TripleColoring n)
    (base : Finset (Fin n)) (hcard : base.card = 5) (q r : Fin n)
    (hqr : q < r) (hafter : ∀ x ∈ base, r < x) : Prop :=
  let e := base.orderEmbOfFin hcard
  ∃ (y : Fin n) (_hy : y ∈ base) (hfirstY : e 0 < y),
    χ ⟨q, e 0, y, hqr.trans (hafter _
        (base.orderEmbOfFin_mem hcard 0)), hfirstY⟩ ≠
      χ ⟨r, e 0, y, hafter _
        (base.orderEmbOfFin_mem hcard 0), hfirstY⟩

/-- A first-middle discrepancy between two strong extensions persists across
the whole common base and forces the external-pair profile to be constant. -/
theorem firstMiddleExtensionDisagreement_forces_constantPairProfile
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n} (hcard : base.card = 5) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) (hbaseSub : base ⊆ ambient)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hfirst : HasFirstMiddleExtensionDisagreement χ base hcard q r hqr
      hafter) :
    IsConstantPairProfile χ base q r hqr hafter := by
  let e : Fin 5 ↪o Fin n := base.orderEmbOfFin hcard
  have heMem (i : Fin 5) : e i ∈ base :=
    base.orderEmbOfFin_mem hcard i
  have heImage : Finset.univ.image e = base :=
    Finset.image_orderEmbOfFin_univ base hcard
  have firstLe {x : Fin n} (hx : x ∈ base) : e 0 ≤ x := by
    have hxImage : x ∈ Finset.univ.image e := by simpa [heImage] using hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxImage
    exact e.monotone (Fin.zero_le i)
  change ∃ (y : Fin n) (_hy : y ∈ base) (hfirstY : e 0 < y),
    χ ⟨q, e 0, y, hqr.trans (hafter _ (heMem 0)), hfirstY⟩ ≠
      χ ⟨r, e 0, y, hafter _ (heMem 0), hfirstY⟩ at hfirst
  obtain ⟨y, hy, hfirstY, hdiff⟩ := hfirst
  have hqMiddle : IsMiddleDeterminedOn χ (insert q base) :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hqStrong
  have hrMiddle : IsMiddleDeterminedOn χ (insert r base) :=
    FinsetPolygon.isStrongPolygonSet_iff_isMiddleDeterminedOn.mp hrStrong
  have pairFirstEq {x : Fin n} (hx : x ∈ base) :
      χ ⟨q, r, e 0, hqr, hafter _ (heMem 0)⟩ =
        χ ⟨q, r, x, hqr, hafter x hx⟩ := by
    by_cases hxFirst : x = e 0
    · subst x
      rfl
    · have hfirstX : e 0 < x :=
        lt_of_le_of_ne (firstLe hx) (Ne.symm hxFirst)
      have hqEq := hqMiddle
        (hqr.trans (hafter _ (heMem 0)))
        (hqr.trans (hafter _ (heMem 0))) hfirstX hfirstY
        (Finset.mem_insert_self q base) (Finset.mem_insert_self q base)
        (Finset.mem_insert_of_mem (heMem 0)) (Finset.mem_insert_of_mem hx)
        (Finset.mem_insert_of_mem hy)
      have hrEq := hrMiddle (hafter _ (heMem 0))
        (hafter _ (heMem 0)) hfirstX hfirstY
        (Finset.mem_insert_self r base) (Finset.mem_insert_self r base)
        (Finset.mem_insert_of_mem (heMem 0)) (Finset.mem_insert_of_mem hx)
        (Finset.mem_insert_of_mem hy)
      have hdiffX :
          χ ⟨q, e 0, x, hqr.trans (hafter _ (heMem 0)), hfirstX⟩ ≠
            χ ⟨r, e 0, x, hafter _ (heMem 0), hfirstX⟩ := by
        intro heq
        exact hdiff (hqEq.symm.trans (heq.trans hrEq))
      exact (sharedStrongResidue_disagreement_forces_pairColors hqr
        (hafter _ (heMem 0)) hfirstX hqAmbient hrAmbient
        (hbaseSub (heMem 0)) (hbaseSub hx) hone hdiffX).1
  intro x hx y hy
  exact (pairFirstEq hx).symm.trans (pairFirstEq hy)

/-- Exact normalized obstruction for a shared strong-five residue in the
no-strong-seven branch: either the external-pair profile varies, or the two
extensions disagree at the first base middle. -/
theorem sharedStrongFiveResidue_pairVariation_or_firstMiddleDisagreement
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n} (hcard : base.card = 5) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) (hbaseSub : base ⊆ ambient)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 7) :
    ¬IsConstantPairProfile χ base q r hqr hafter ∨
      HasFirstMiddleExtensionDisagreement χ base hcard q r hqr hafter := by
  rcases sharedStrongFiveResidue_pairVariation_or_extensionDisagreement
      hcard hqr hafter hbaseSub hqAmbient hrAmbient hqStrong hrStrong
      hnoStrong with hpair | hext
  · exact Or.inl hpair
  · apply Or.inr
    let e : Fin 5 ↪o Fin n := base.orderEmbOfFin hcard
    have heMem (i : Fin 5) : e i ∈ base :=
      base.orderEmbOfFin_mem hcard i
    have heImage : Finset.univ.image e = base :=
      Finset.image_orderEmbOfFin_univ base hcard
    have firstLe {x : Fin n} (hx : x ∈ base) : e 0 ≤ x := by
      have hxImage : x ∈ Finset.univ.image e := by simpa [heImage] using hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hxImage
      exact e.monotone (Fin.zero_le i)
    by_contra hfirst
    apply hext
    intro x hx y hy hxy
    by_cases hxFirst : x = e 0
    · subst x
      by_contra hdiff
      exact hfirst ⟨y, hy, hxy, hdiff⟩
    · have hfirstX : e 0 < x :=
        lt_of_le_of_ne (firstLe hx) (Ne.symm hxFirst)
      exact sharedStrongResidue_laterMiddle_extensionColors_eq
        hqr (hafter _ (heMem 0)) hfirstX hxy (heMem 0) hx hy
        hqStrong hrStrong

/-- Exact two-state classification for a shared strong-five residue in the
one-change, no-strong-seven branch. Pair variation occurs precisely in the
no-first-disagreement state; a first disagreement forces a constant profile. -/
theorem sharedStrongFiveResidue_exact_dichotomy
    {n : ℕ} {χ : TripleColoring n} {ambient base : Finset (Fin n)}
    {q r : Fin n} (hcard : base.card = 5) (hqr : q < r)
    (hafter : ∀ x ∈ base, r < x) (hbaseSub : base ⊆ ambient)
    (hqAmbient : q ∈ ambient) (hrAmbient : r ∈ ambient)
    (hone : OneChangeOn χ ambient)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hnoStrong : ¬ContainsStrongPolygonSet χ ambient 7) :
    (¬IsConstantPairProfile χ base q r hqr hafter ∧
      ¬HasFirstMiddleExtensionDisagreement χ base hcard q r hqr hafter) ∨
    (IsConstantPairProfile χ base q r hqr hafter ∧
      HasFirstMiddleExtensionDisagreement χ base hcard q r hqr hafter) := by
  rcases sharedStrongFiveResidue_pairVariation_or_firstMiddleDisagreement
      hcard hqr hafter hbaseSub hqAmbient hrAmbient hqStrong hrStrong
      hnoStrong with hpair | hfirst
  · exact Or.inl ⟨hpair, fun hfirst ↦ hpair
      (firstMiddleExtensionDisagreement_forces_constantPairProfile
        hcard hqr hafter hbaseSub hqAmbient hrAmbient hone hqStrong
        hrStrong hfirst)⟩
  · exact Or.inr
      ⟨firstMiddleExtensionDisagreement_forces_constantPairProfile
        hcard hqr hafter hbaseSub hqAmbient hrAmbient hone hqStrong
        hrStrong hfirst, hfirst⟩

/-- Ordered-cut application of the shared-cap transition: two left-side
vertices using the same three-residue on the right have a right-monotone pair
profile. -/
theorem leftPair_sharedCapResidue_pairProfile_rightMonotone
    {n : ℕ} {χ : TripleColoring n}
    {left right base : Finset (Fin n)} {q r : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hqLeft : q ∈ left) (hrLeft : r ∈ left) (hqr : q < r)
    (hbaseSub : base ⊆ right) (hone : OneChangeOn χ (left ∪ right))
    (hqCap : IsCapSet χ (insert q base))
    (hrCap : IsCapSet χ (insert r base)) :
    let hafter : ∀ x ∈ base, r < x :=
      fun x hx ↦ horder r hrLeft x (hbaseSub hx)
    IsRightMonotonePairProfile χ base q r hqr hafter := by
  dsimp only
  apply sharedCapResidue_pairProfile_rightMonotone hqr
    (fun x hx ↦ horder r hrLeft x (hbaseSub hx))
    (hbaseSub.trans Finset.subset_union_right)
    (Finset.mem_union_left right hqLeft) (Finset.mem_union_left right hrLeft)
    hone hqCap hrCap

/-- Mirror ordered-cut application for two right-side vertices sharing a cap
residue on the left. -/
theorem rightPair_sharedCapResidue_pairProfile_leftMonotone
    {n : ℕ} {χ : TripleColoring n}
    {left right base : Finset (Fin n)} {q r : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hqRight : q ∈ right) (hrRight : r ∈ right) (hqr : q < r)
    (hbaseSub : base ⊆ left) (hone : OneChangeOn χ (left ∪ right))
    (hqCap : IsCapSet χ (insert q base))
    (hrCap : IsCapSet χ (insert r base)) :
    let hbefore : ∀ x ∈ base, x < q :=
      fun x hx ↦ horder x (hbaseSub hx) q hqRight
    IsLeftMonotonePairProfileBefore χ base q r hqr hbefore := by
  dsimp only
  apply sharedCapResidue_pairProfile_leftMonotone_before hqr
    (fun x hx ↦ horder x (hbaseSub hx) q hqRight)
    (hbaseSub.trans Finset.subset_union_left)
    (Finset.mem_union_right left hqRight) (Finset.mem_union_right left hrRight)
    hone hqCap hrCap

/-- Ordered-cut application of the normalized shared-strong-residue
obstruction in the balanced branch. -/
theorem leftPair_sharedStrongFiveResidue_normalized_obstruction
    {n : ℕ} {χ : TripleColoring n}
    {left right base : Finset (Fin n)} {q r : Fin n}
    (horder : ∀ x ∈ left, ∀ y ∈ right, x < y)
    (hqLeft : q ∈ left) (hrLeft : r ∈ left) (hqr : q < r)
    (hbaseSub : base ⊆ right) (hcard : base.card = 5)
    (hqStrong : IsStrongPolygonSet χ (insert q base))
    (hrStrong : IsStrongPolygonSet χ (insert r base))
    (hnoStrong : ¬ContainsStrongPolygonSet χ (left ∪ right) 7) :
    let hafter : ∀ x ∈ base, r < x :=
      fun x hx ↦ horder r hrLeft x (hbaseSub hx)
    ¬IsConstantPairProfile χ base q r hqr hafter ∨
      HasFirstMiddleExtensionDisagreement χ base hcard q r hqr hafter := by
  dsimp only
  apply sharedStrongFiveResidue_pairVariation_or_firstMiddleDisagreement
    hcard hqr (fun x hx ↦ horder r hrLeft x (hbaseSub hx))
    (hbaseSub.trans Finset.subset_union_right)
    (Finset.mem_union_left right hqLeft) (Finset.mem_union_left right hrLeft)
    hqStrong hrStrong hnoStrong

end ErdosSzekeres

end
