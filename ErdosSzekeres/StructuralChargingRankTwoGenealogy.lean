module

public import ErdosSzekeres.StructuralChargingTransitionHall
public import Mathlib.Data.Bool.Count
public import Mathlib.Data.List.Destutter

@[expose] public section

/-!
# Rank-two gap genealogies

The rank-two frontier records child changes in the sweep-ordered merge word.
An adjacency inherited from one child can disappear at its parent only when a
vertex of the other child lies between its endpoints.  Such a hidden child
gap is not lost combinatorial mass: the deep-below law turns it into an actual
rank-three witness of the color determined by the intervening child.

This is the first cross-rank bridge needed by a possible coupled replacement
for the refuted per-rank rank-two Pascal allocation.  It does not assert that
the resulting witnesses are distinct or support a global slotting.
-/

namespace ErdosSzekeres

noncomputable section

/-- The alternating run word of a binary child-membership word. -/
def binaryRunWord (word : List Bool) : List Bool :=
  word.destutter (· ≠ ·)

/-- Adjacent parent crossings are the boundaries between binary runs. -/
def binaryCrossingGapCount (word : List Bool) : ℕ :=
  (binaryRunWord word).length - 1

/-- Apart from its first run, every run of either child begins after a child
gap that has been hidden by a run of the other child. -/
def binaryHiddenChildGapCount (word : List Bool) : ℕ :=
  (binaryRunWord word).count false - 1 +
    ((binaryRunWord word).count true - 1)

/-- In a merge containing both children, the number of adjacent crossings is
one plus the number of hidden child gaps.  This is the elementary accounting
identity behind the proposed genealogy carrier. -/
theorem binaryCrossingGapCount_eq_hiddenChildGapCount_add_one
    (word : List Bool) (hfalse : false ∈ binaryRunWord word)
    (htrue : true ∈ binaryRunWord word) :
    binaryCrossingGapCount word = binaryHiddenChildGapCount word + 1 := by
  have hfalsePos : 0 < (binaryRunWord word).count false :=
    List.count_pos_iff.mpr hfalse
  have htruePos : 0 < (binaryRunWord word).count true :=
    List.count_pos_iff.mpr htrue
  have htotal := List.count_false_add_count_true (binaryRunWord word)
  simp only [binaryCrossingGapCount, binaryHiddenChildGapCount]
  omega

/-- Two endpoints are consecutive inside a specified sweep-ordered support. -/
def SweepSpanEndpoints.IsAdjacentIn {n : ℕ} (span : SweepSpanEndpoints n)
    (support : Finset (Fin n)) : Prop :=
  span.left < span.right ∧ span.left ∈ support ∧ span.right ∈ support ∧
    ∀ q ∈ support, ¬(span.left < q ∧ q < span.right)

/-- An adjacency is determined by its right endpoint inside a fixed support. -/
theorem SweepSpanEndpoints.IsAdjacentIn.eq_of_right_eq
    {n : ℕ} {support : Finset (Fin n)}
    {first second : SweepSpanEndpoints n}
    (hfirst : first.IsAdjacentIn support)
    (hsecond : second.IsAdjacentIn support)
    (hright : first.right = second.right) : first = second := by
  have hleft : first.left = second.left := by
    rcases lt_trichotomy first.left second.left with hlt | heq | hgt
    · exfalso
      apply hfirst.2.2.2 second.left hsecond.2.1
      exact ⟨hlt, by simpa [hright] using hsecond.1⟩
    · exact heq
    · exfalso
      apply hsecond.2.2.2 first.left hfirst.2.1
      exact ⟨hgt, by simpa [hright] using hfirst.1⟩
  cases first
  cases second
  simp_all

/-- Dually, an adjacency is determined by its left endpoint. -/
theorem SweepSpanEndpoints.IsAdjacentIn.eq_of_left_eq
    {n : ℕ} {support : Finset (Fin n)}
    {first second : SweepSpanEndpoints n}
    (hfirst : first.IsAdjacentIn support)
    (hsecond : second.IsAdjacentIn support)
    (hleft : first.left = second.left) : first = second := by
  have hright : first.right = second.right := by
    rcases lt_trichotomy first.right second.right with hlt | heq | hgt
    · exfalso
      apply hsecond.2.2.2 first.right hfirst.2.2.1
      exact ⟨by simpa [hleft] using hfirst.1, hlt⟩
    · exact heq
    · exfalso
      apply hfirst.2.2.2 second.right hsecond.2.2.1
      exact ⟨by simpa [hleft] using hsecond.1, hgt⟩
  cases first
  cases second
  simp_all

/-- A lower-child adjacency hidden at the parent by an upper-child vertex. -/
def IsHiddenLowerGap {n : ℕ} (lower upper : Finset (Fin n))
    (span : SweepSpanEndpoints n) : Prop :=
  span.IsAdjacentIn lower ∧
    ∃ q ∈ upper, span.left < q ∧ q < span.right

/-- An upper-child adjacency hidden at the parent by a lower-child vertex. -/
def IsHiddenUpperGap {n : ℕ} (lower upper : Finset (Fin n))
    (span : SweepSpanEndpoints n) : Prop :=
  span.IsAdjacentIn upper ∧
    ∃ q ∈ lower, span.left < q ∧ q < span.right

/-- The finite source family compatible with a fixed promoted color. Caps use
hidden lower gaps; cups use hidden upper gaps. -/
noncomputable def hiddenGapSources {n : ℕ}
    (lower upper : Finset (Fin n)) :
    Turn → Finset (SweepSpanEndpoints n) := by
  classical
  exact fun color => match color with
    | .left => Finset.univ.filter (IsHiddenUpperGap lower upper)
    | .right => Finset.univ.filter (IsHiddenLowerGap lower upper)

theorem mem_hiddenGapSources_iff {n : ℕ} {lower upper : Finset (Fin n)}
    {color : Turn} {span : SweepSpanEndpoints n} :
    span ∈ hiddenGapSources lower upper color ↔
      match color with
      | .left => IsHiddenUpperGap lower upper span
      | .right => IsHiddenLowerGap lower upper span := by
  cases color <;> simp [hiddenGapSources]

/-- A sweep adjacency in the parent support whose endpoints cross the split. -/
def IsParentCrossingGap {n : ℕ} (lower upper : Finset (Fin n))
    (span : SweepSpanEndpoints n) : Prop :=
  span.IsAdjacentIn (lower ∪ upper) ∧ span.CrossesSplit lower upper

noncomputable def parentCrossingGaps {n : ℕ}
    (lower upper : Finset (Fin n)) : Finset (SweepSpanEndpoints n) := by
  classical
  exact Finset.univ.filter (IsParentCrossingGap lower upper)

theorem mem_parentCrossingGaps_iff
    {n : ℕ} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} :
    span ∈ parentCrossingGaps lower upper ↔
      IsParentCrossingGap lower upper span := by
  classical
  simp [parentCrossingGaps]

/-- Parent adjacencies with the same right endpoint are identical. -/
theorem IsParentCrossingGap.eq_of_right_eq
    {n : ℕ} {lower upper : Finset (Fin n)}
    {first second : SweepSpanEndpoints n}
    (hfirst : IsParentCrossingGap lower upper first)
    (hsecond : IsParentCrossingGap lower upper second)
    (hright : first.right = second.right) : first = second := by
  have hleft : first.left = second.left := by
    rcases lt_trichotomy first.left second.left with hlt | heq | hgt
    · exfalso
      apply hfirst.1.2.2.2 second.left hsecond.1.2.1
      exact ⟨hlt, by simpa [hright] using hsecond.1.1⟩
    · exact heq
    · exfalso
      apply hsecond.1.2.2.2 first.left hfirst.1.2.1
      exact ⟨hgt, by simpa [hright] using hfirst.1.1⟩
  cases first
  cases second
  simp_all

/-- A hidden lower gap has a unique parent crossing gap entering its right
endpoint. Existence uses the rightmost intervening upper vertex. -/
theorem IsHiddenLowerGap.exists_unique_enteringParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hgap : IsHiddenLowerGap lower upper span) :
    ∃ target : SweepSpanEndpoints n,
      IsParentCrossingGap lower upper target ∧
        target.right = span.right ∧
        ∀ other : SweepSpanEndpoints n,
          IsParentCrossingGap lower upper other →
          other.right = span.right → other = target := by
  classical
  obtain ⟨hadj, q0, hq0Upper, hleftq0, hq0right⟩ := hgap
  let between := upper.filter fun q => span.left < q ∧ q < span.right
  have hbetween : between.Nonempty := by
    refine ⟨q0, Finset.mem_filter.mpr ⟨hq0Upper, hleftq0, hq0right⟩⟩
  let q := between.max' hbetween
  have hqBetween : q ∈ between := Finset.max'_mem between hbetween
  have hqData := Finset.mem_filter.mp hqBetween
  have hqUpper : q ∈ upper := hqData.1
  have hleftq : span.left < q := hqData.2.1
  have hqright : q < span.right := hqData.2.2
  have hrightLower : span.right ∈ lower := hadj.2.2.1
  let target : SweepSpanEndpoints n := ⟨q, span.right⟩
  have htarget : IsParentCrossingGap lower upper target := by
    constructor
    · refine ⟨hqright, Finset.mem_union_right lower hqUpper,
        Finset.mem_union_left upper hrightLower, ?_⟩
      intro x hxSupport hxInside
      have hqx : q < x := by simpa [target] using hxInside.1
      have hxr : x < span.right := by simpa [target] using hxInside.2
      rcases Finset.mem_union.mp hxSupport with hxLower | hxUpper
      · exact hadj.2.2.2 x hxLower ⟨hleftq.trans hqx, hxr⟩
      · have hxBetween : x ∈ between := by
          exact Finset.mem_filter.mpr
            ⟨hxUpper, hleftq.trans hqx, hxr⟩
        have hxq : x ≤ q := Finset.le_max' between x hxBetween
        exact (not_lt_of_ge hxq) hqx
    · simpa [target, SweepSpanEndpoints.CrossesSplit] using
        (⟨hqright, Or.inr ⟨hqUpper, hrightLower⟩⟩ :
          q < span.right ∧
            ((q ∈ lower ∧ span.right ∈ upper) ∨
              (q ∈ upper ∧ span.right ∈ lower)))
  refine ⟨target, htarget, rfl, ?_⟩
  intro other hother hotherRight
  exact hother.eq_of_right_eq htarget hotherRight

/-- Color-dual entering-transition theorem for a hidden upper gap. -/
theorem IsHiddenUpperGap.exists_unique_enteringParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hgap : IsHiddenUpperGap lower upper span) :
    ∃ target : SweepSpanEndpoints n,
      IsParentCrossingGap lower upper target ∧
        target.right = span.right ∧
        ∀ other : SweepSpanEndpoints n,
          IsParentCrossingGap lower upper other →
          other.right = span.right → other = target := by
  classical
  obtain ⟨hadj, q0, hq0Lower, hleftq0, hq0right⟩ := hgap
  let between := lower.filter fun q => span.left < q ∧ q < span.right
  have hbetween : between.Nonempty := by
    refine ⟨q0, Finset.mem_filter.mpr ⟨hq0Lower, hleftq0, hq0right⟩⟩
  let q := between.max' hbetween
  have hqBetween : q ∈ between := Finset.max'_mem between hbetween
  have hqData := Finset.mem_filter.mp hqBetween
  have hqLower : q ∈ lower := hqData.1
  have hleftq : span.left < q := hqData.2.1
  have hqright : q < span.right := hqData.2.2
  have hrightUpper : span.right ∈ upper := hadj.2.2.1
  let target : SweepSpanEndpoints n := ⟨q, span.right⟩
  have htarget : IsParentCrossingGap lower upper target := by
    constructor
    · refine ⟨hqright, Finset.mem_union_left upper hqLower,
        Finset.mem_union_right lower hrightUpper, ?_⟩
      intro x hxSupport hxInside
      have hqx : q < x := by simpa [target] using hxInside.1
      have hxr : x < span.right := by simpa [target] using hxInside.2
      rcases Finset.mem_union.mp hxSupport with hxLower | hxUpper
      · have hxBetween : x ∈ between := by
          exact Finset.mem_filter.mpr
            ⟨hxLower, hleftq.trans hqx, hxr⟩
        have hxq : x ≤ q := Finset.le_max' between x hxBetween
        exact (not_lt_of_ge hxq) hqx
      · exact hadj.2.2.2 x hxUpper ⟨hleftq.trans hqx, hxr⟩
    · simpa [target, SweepSpanEndpoints.CrossesSplit] using
        (⟨hqright, Or.inl ⟨hqLower, hrightUpper⟩⟩ :
          q < span.right ∧
            ((q ∈ lower ∧ span.right ∈ upper) ∨
              (q ∈ upper ∧ span.right ∈ lower)))
  refine ⟨target, htarget, rfl, ?_⟩
  intro other hother hotherRight
  exact hother.eq_of_right_eq htarget hotherRight

abbrev HiddenGapSource {n : ℕ} (lower upper : Finset (Fin n))
    (color : Turn) := {span // span ∈ hiddenGapSources lower upper color}

abbrev ParentCrossingGap {n : ℕ} (lower upper : Finset (Fin n)) :=
  {span // span ∈ parentCrossingGaps lower upper}

theorem hiddenGapSource_exists_unique_enteringParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn}
    (source : HiddenGapSource lower upper color) :
    ∃ target : SweepSpanEndpoints n,
      IsParentCrossingGap lower upper target ∧
        target.right = source.1.right ∧
        ∀ other : SweepSpanEndpoints n,
          IsParentCrossingGap lower upper other →
          other.right = source.1.right → other = target := by
  have hsource := (mem_hiddenGapSources_iff.mp source.2)
  cases color with
  | left => exact hsource.exists_unique_enteringParentCrossingGap
  | right => exact hsource.exists_unique_enteringParentCrossingGap

/-- The canonical parent transition entering the run that ends a hidden
color-compatible child gap. -/
noncomputable def HiddenGapSource.enteringParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn}
    (source : HiddenGapSource lower upper color) :
    ParentCrossingGap lower upper := by
  classical
  let target := Classical.choose
    (hiddenGapSource_exists_unique_enteringParentCrossingGap source)
  exact ⟨target,
    mem_parentCrossingGaps_iff.mpr
      (Classical.choose_spec
        (hiddenGapSource_exists_unique_enteringParentCrossingGap source)).1⟩

theorem HiddenGapSource.enteringParentCrossingGap_right
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn}
    (source : HiddenGapSource lower upper color) :
    source.enteringParentCrossingGap.1.right = source.1.right := by
  classical
  change (Classical.choose
    (hiddenGapSource_exists_unique_enteringParentCrossingGap source)).right =
      source.1.right
  exact (Classical.choose_spec
    (hiddenGapSource_exists_unique_enteringParentCrossingGap source)).2.1

/-- The entering transition starts strictly after the left endpoint of its
hidden source gap. -/
theorem HiddenGapSource.left_lt_enteringParentCrossingGap_left
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn}
    (source : HiddenGapSource lower upper color) :
    source.1.left < source.enteringParentCrossingGap.1.left := by
  have henter := mem_parentCrossingGaps_iff.mp
    source.enteringParentCrossingGap.2
  have hsource := mem_hiddenGapSources_iff.mp source.2
  cases color with
  | left =>
      obtain ⟨_, q, hqLower, hleftq, hqright⟩ := hsource
      have hqSupport : q ∈ lower ∪ upper :=
        Finset.mem_union_left upper hqLower
      have hqEnterRight : q < source.enteringParentCrossingGap.1.right := by
        simpa [source.enteringParentCrossingGap_right] using hqright
      have hqLe : q ≤ source.enteringParentCrossingGap.1.left := by
        by_contra hnot
        apply henter.1.2.2.2 q hqSupport
        exact ⟨by omega, hqEnterRight⟩
      exact hleftq.trans_le hqLe
  | right =>
      obtain ⟨_, q, hqUpper, hleftq, hqright⟩ := hsource
      have hqSupport : q ∈ lower ∪ upper :=
        Finset.mem_union_right lower hqUpper
      have hqEnterRight : q < source.enteringParentCrossingGap.1.right := by
        simpa [source.enteringParentCrossingGap_right] using hqright
      have hqLe : q ≤ source.enteringParentCrossingGap.1.left := by
        by_contra hnot
        apply henter.1.2.2.2 q hqSupport
        exact ⟨by omega, hqEnterRight⟩
      exact hleftq.trans_le hqLe

/-- Distinct compatible hidden gaps have distinct entering parent
transitions. -/
theorem HiddenGapSource.enteringParentCrossingGap_injective
    {n : ℕ} {lower upper : Finset (Fin n)} {color : Turn} :
    Function.Injective
      (HiddenGapSource.enteringParentCrossingGap
        (lower := lower) (upper := upper) (color := color)) := by
  intro first second htarget
  apply Subtype.ext
  have hright : first.1.right = second.1.right := by
    rw [← first.enteringParentCrossingGap_right,
      ← second.enteringParentCrossingGap_right]
    exact congrArg (fun target : ParentCrossingGap lower upper =>
      target.1.right) htarget
  have hfirst := mem_hiddenGapSources_iff.mp first.2
  have hsecond := mem_hiddenGapSources_iff.mp second.2
  cases color with
  | left => exact hfirst.1.eq_of_right_eq hsecond.1 hright
  | right => exact hfirst.1.eq_of_right_eq hsecond.1 hright

/-- The canonical entering-transition injection. -/
noncomputable def hiddenGapSourceEnteringEmbedding
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    HiddenGapSource lower upper color ↪ ParentCrossingGap lower upper :=
  ⟨HiddenGapSource.enteringParentCrossingGap,
    HiddenGapSource.enteringParentCrossingGap_injective⟩

/-- Hence the color-compatible hidden source family never has more elements
than the parent crossing-gap family. The desired exact identity additionally
needs a distinguished crossing outside this image. -/
theorem hiddenGapSource_card_le_parentCrossingGap_card
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    Fintype.card (HiddenGapSource lower upper color) ≤
      Fintype.card (ParentCrossingGap lower upper) := by
  classical
  exact Fintype.card_le_of_embedding
    (hiddenGapSourceEnteringEmbedding lower upper color)

/-- Both promoted colors together enumerate all hidden child gaps. -/
abbrev AllHiddenGapSource {n : ℕ} (lower upper : Finset (Fin n)) :=
  HiddenGapSource lower upper .left ⊕ HiddenGapSource lower upper .right

noncomputable def allHiddenGapSourceEntering
    {n : ℕ} {lower upper : Finset (Fin n)} :
    AllHiddenGapSource lower upper → ParentCrossingGap lower upper
  | .inl source => source.enteringParentCrossingGap
  | .inr source => source.enteringParentCrossingGap

/-- With disjoint children, the cup- and cap-compatible source injections
also have disjoint images, so their union embeds into the crossing gaps. -/
theorem allHiddenGapSourceEntering_injective
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper) :
    Function.Injective
      (allHiddenGapSourceEntering (lower := lower) (upper := upper)) := by
  intro first second heq
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          congr 1
          exact HiddenGapSource.enteringParentCrossingGap_injective heq
      | inr second =>
          exfalso
          have hright : first.1.right = second.1.right := by
            rw [← first.enteringParentCrossingGap_right,
              ← second.enteringParentCrossingGap_right]
            exact congrArg (fun target : ParentCrossingGap lower upper =>
              target.1.right) heq
          have hfirst := mem_hiddenGapSources_iff.mp first.2
          have hsecond := mem_hiddenGapSources_iff.mp second.2
          exact (Finset.disjoint_left.mp hdisjoint hsecond.1.2.2.1
            (hright ▸ hfirst.1.2.2.1)).elim
  | inr first =>
      cases second with
      | inl second =>
          exfalso
          have hright : first.1.right = second.1.right := by
            rw [← first.enteringParentCrossingGap_right,
              ← second.enteringParentCrossingGap_right]
            exact congrArg (fun target : ParentCrossingGap lower upper =>
              target.1.right) heq
          have hfirst := mem_hiddenGapSources_iff.mp first.2
          have hsecond := mem_hiddenGapSources_iff.mp second.2
          exact (Finset.disjoint_left.mp hdisjoint hfirst.1.2.2.1
            (hright ▸ hsecond.1.2.2.1)).elim
      | inr second =>
          congr 1
          exact HiddenGapSource.enteringParentCrossingGap_injective heq

noncomputable def allHiddenGapSourceEnteringEmbedding
    {n : ℕ} (lower upper : Finset (Fin n))
    (hdisjoint : Disjoint lower upper) :
    AllHiddenGapSource lower upper ↪ ParentCrossingGap lower upper :=
  ⟨allHiddenGapSourceEntering,
    allHiddenGapSourceEntering_injective hdisjoint⟩

theorem allHiddenGapSource_card_le_parentCrossingGap_card
    {n : ℕ} (lower upper : Finset (Fin n))
    (hdisjoint : Disjoint lower upper) :
    Fintype.card (AllHiddenGapSource lower upper) ≤
      Fintype.card (ParentCrossingGap lower upper) := by
  exact Fintype.card_le_of_embedding
    (allHiddenGapSourceEnteringEmbedding lower upper hdisjoint)

/-- Every lower-to-upper parent crossing after an earlier upper run is the
entering transition of a hidden upper gap. -/
theorem IsParentCrossingGap.exists_hiddenUpperSource_of_prior_upper
    {n : ℕ} {lower upper : Finset (Fin n)}
    {target : SweepSpanEndpoints n}
    (hdisjoint : Disjoint lower upper)
    (htarget : IsParentCrossingGap lower upper target)
    (hsides : target.left ∈ lower ∧ target.right ∈ upper)
    (hprior : ∃ a ∈ upper, a < target.left) :
    ∃ source : HiddenGapSource lower upper .left,
      source.enteringParentCrossingGap.1 = target := by
  classical
  let before := upper.filter fun a => a < target.left
  have hbefore : before.Nonempty := by
    obtain ⟨a, haUpper, haLeft⟩ := hprior
    exact ⟨a, Finset.mem_filter.mpr ⟨haUpper, haLeft⟩⟩
  let a := before.max' hbefore
  have haBefore : a ∈ before := Finset.max'_mem before hbefore
  have haData := Finset.mem_filter.mp haBefore
  have haUpper : a ∈ upper := haData.1
  have haLeft : a < target.left := haData.2
  let span : SweepSpanEndpoints n := ⟨a, target.right⟩
  have hhidden : IsHiddenUpperGap lower upper span := by
    constructor
    · refine ⟨haLeft.trans htarget.1.1, haUpper, hsides.2, ?_⟩
      intro x hxUpper hxInside
      have hax : a < x := by simpa [span] using hxInside.1
      have hxRight : x < target.right := by simpa [span] using hxInside.2
      rcases lt_trichotomy x target.left with hxLeft | hxeq | hxAfter
      · have hxBefore : x ∈ before :=
          Finset.mem_filter.mpr ⟨hxUpper, hxLeft⟩
        exact (not_lt_of_ge (Finset.le_max' before x hxBefore)) hax
      · subst x
        exact (Finset.disjoint_left.mp hdisjoint hsides.1 hxUpper).elim
      · exact htarget.1.2.2.2 x
          (Finset.mem_union_right lower hxUpper) ⟨hxAfter, hxRight⟩
    · exact ⟨target.left, hsides.1, haLeft, htarget.1.1⟩
  let source : HiddenGapSource lower upper .left :=
    ⟨span, mem_hiddenGapSources_iff.mpr hhidden⟩
  refine ⟨source, ?_⟩
  apply IsParentCrossingGap.eq_of_right_eq
    (mem_parentCrossingGaps_iff.mp source.enteringParentCrossingGap.2)
    htarget
  exact source.enteringParentCrossingGap_right

/-- Color-dual inverse: every upper-to-lower crossing after an earlier lower
run is the entering transition of a hidden lower gap. -/
theorem IsParentCrossingGap.exists_hiddenLowerSource_of_prior_lower
    {n : ℕ} {lower upper : Finset (Fin n)}
    {target : SweepSpanEndpoints n}
    (hdisjoint : Disjoint lower upper)
    (htarget : IsParentCrossingGap lower upper target)
    (hsides : target.left ∈ upper ∧ target.right ∈ lower)
    (hprior : ∃ a ∈ lower, a < target.left) :
    ∃ source : HiddenGapSource lower upper .right,
      source.enteringParentCrossingGap.1 = target := by
  classical
  let before := lower.filter fun a => a < target.left
  have hbefore : before.Nonempty := by
    obtain ⟨a, haLower, haLeft⟩ := hprior
    exact ⟨a, Finset.mem_filter.mpr ⟨haLower, haLeft⟩⟩
  let a := before.max' hbefore
  have haBefore : a ∈ before := Finset.max'_mem before hbefore
  have haData := Finset.mem_filter.mp haBefore
  have haLower : a ∈ lower := haData.1
  have haLeft : a < target.left := haData.2
  let span : SweepSpanEndpoints n := ⟨a, target.right⟩
  have hhidden : IsHiddenLowerGap lower upper span := by
    constructor
    · refine ⟨haLeft.trans htarget.1.1, haLower, hsides.2, ?_⟩
      intro x hxLower hxInside
      have hax : a < x := by simpa [span] using hxInside.1
      have hxRight : x < target.right := by simpa [span] using hxInside.2
      rcases lt_trichotomy x target.left with hxLeft | hxeq | hxAfter
      · have hxBefore : x ∈ before :=
          Finset.mem_filter.mpr ⟨hxLower, hxLeft⟩
        exact (not_lt_of_ge (Finset.le_max' before x hxBefore)) hax
      · subst x
        exact (Finset.disjoint_left.mp hdisjoint hxLower hsides.1).elim
      · exact htarget.1.2.2.2 x
          (Finset.mem_union_left upper hxLower) ⟨hxAfter, hxRight⟩
    · exact ⟨target.left, hsides.1, haLeft, htarget.1.1⟩
  let source : HiddenGapSource lower upper .right :=
    ⟨span, mem_hiddenGapSources_iff.mpr hhidden⟩
  refine ⟨source, ?_⟩
  apply IsParentCrossingGap.eq_of_right_eq
    (mem_parentCrossingGaps_iff.mp source.enteringParentCrossingGap.2)
    htarget
  exact source.enteringParentCrossingGap_right

/-- The sole crossing transition not created by a hidden child gap should be
the first change in the binary merge word. This predicate characterizes such
a transition without choosing a sorted-list representation: the child entered
at its right endpoint has no vertex before the left endpoint. -/
def IsInitialParentCrossingGap {n : ℕ}
    (lower upper : Finset (Fin n)) (target : SweepSpanEndpoints n) : Prop :=
  (target.right ∈ lower → ¬∃ a ∈ lower, a < target.left) ∧
    (target.right ∈ upper → ¬∃ a ∈ upper, a < target.left)

/-- There is at most one initial crossing in a disjoint binary merge. -/
theorem IsInitialParentCrossingGap.eq
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper)
    {first second : SweepSpanEndpoints n}
    (hfirstGap : IsParentCrossingGap lower upper first)
    (hsecondGap : IsParentCrossingGap lower upper second)
    (hfirstInitial : IsInitialParentCrossingGap lower upper first)
    (hsecondInitial : IsInitialParentCrossingGap lower upper second) :
    first = second := by
  have hleft : first.left = second.left := by
    rcases lt_trichotomy first.left second.left with hlt | heq | hgt
    · exfalso
      have hrightLe : first.right ≤ second.left := by
        by_contra hnot
        apply hfirstGap.1.2.2.2 second.left hsecondGap.1.2.1
        exact ⟨hlt, by omega⟩
      rcases hsecondGap.2.2 with hsecondSides | hsecondSides
      · rcases hfirstGap.2.2 with hfirstSides | hfirstSides
        · apply hsecondInitial.2 hsecondSides.2
          exact ⟨first.right, hfirstSides.2, by
            have hne : first.right ≠ second.left := by
              intro heqRight
              exact (Finset.disjoint_left.mp hdisjoint hsecondSides.1
                (heqRight ▸ hfirstSides.2)).elim
            omega⟩
        · apply hsecondInitial.2 hsecondSides.2
          exact ⟨first.left, hfirstSides.1, hlt⟩
      · rcases hfirstGap.2.2 with hfirstSides | hfirstSides
        · apply hsecondInitial.1 hsecondSides.2
          exact ⟨first.left, hfirstSides.1, hlt⟩
        · apply hsecondInitial.1 hsecondSides.2
          exact ⟨first.right, hfirstSides.2, by
            have hne : first.right ≠ second.left := by
              intro heqRight
              exact (Finset.disjoint_left.mp hdisjoint
                (heqRight ▸ hfirstSides.2) hsecondSides.1).elim
            omega⟩
    · exact heq
    · exfalso
      have hrightLe : second.right ≤ first.left := by
        by_contra hnot
        apply hsecondGap.1.2.2.2 first.left hfirstGap.1.2.1
        exact ⟨hgt, by omega⟩
      rcases hfirstGap.2.2 with hfirstSides | hfirstSides
      · rcases hsecondGap.2.2 with hsecondSides | hsecondSides
        · apply hfirstInitial.2 hfirstSides.2
          exact ⟨second.right, hsecondSides.2, by
            have hne : second.right ≠ first.left := by
              intro heqRight
              exact (Finset.disjoint_left.mp hdisjoint hfirstSides.1
                (heqRight ▸ hsecondSides.2)).elim
            omega⟩
        · apply hfirstInitial.2 hfirstSides.2
          exact ⟨second.left, hsecondSides.1, hgt⟩
      · rcases hsecondGap.2.2 with hsecondSides | hsecondSides
        · apply hfirstInitial.1 hfirstSides.2
          exact ⟨second.left, hsecondSides.1, hgt⟩
        · apply hfirstInitial.1 hfirstSides.2
          exact ⟨second.right, hsecondSides.2, by
            have hne : second.right ≠ first.left := by
              intro heqRight
              exact (Finset.disjoint_left.mp hdisjoint
                (heqRight ▸ hsecondSides.2) hfirstSides.1).elim
            omega⟩
  exact hfirstGap.1.eq_of_left_eq hsecondGap.1 hleft

/-- A nonempty disjoint binary merge has an initial crossing.  The
construction takes the first vertex of each child and then the last vertex of
the earlier child before the first vertex of the later child. -/
theorem exists_initialParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper) :
    ∃ target : ParentCrossingGap lower upper,
      IsInitialParentCrossingGap lower upper target.1 := by
  classical
  let lmin := lower.min' hlower
  let umin := upper.min' hupper
  have hlminLower : lmin ∈ lower := Finset.min'_mem lower hlower
  have huminUpper : umin ∈ upper := Finset.min'_mem upper hupper
  have hne : lmin ≠ umin := by
    intro heq
    exact (Finset.disjoint_left.mp hdisjoint hlminLower
      (heq ▸ huminUpper)).elim
  rcases lt_or_gt_of_ne hne with hlu | hul
  · let before := lower.filter fun a => a < umin
    have hbefore : before.Nonempty :=
      ⟨lmin, Finset.mem_filter.mpr ⟨hlminLower, hlu⟩⟩
    let a := before.max' hbefore
    have haBefore : a ∈ before := Finset.max'_mem before hbefore
    have haData := Finset.mem_filter.mp haBefore
    have haLower : a ∈ lower := haData.1
    have haUmin : a < umin := haData.2
    let span : SweepSpanEndpoints n := ⟨a, umin⟩
    have hadj : span.IsAdjacentIn (lower ∪ upper) := by
      refine ⟨haUmin, Finset.mem_union_left upper haLower,
        Finset.mem_union_right lower huminUpper, ?_⟩
      intro x hxSupport hxInside
      have hax : a < x := by simpa [span] using hxInside.1
      have hxUmin : x < umin := by simpa [span] using hxInside.2
      rcases Finset.mem_union.mp hxSupport with hxLower | hxUpper
      · have hxBefore : x ∈ before :=
          Finset.mem_filter.mpr ⟨hxLower, hxUmin⟩
        exact (not_lt_of_ge (Finset.le_max' before x hxBefore)) hax
      · exact (not_lt_of_ge (Finset.min'_le upper x hxUpper)) hxUmin
    have hcross : span.CrossesSplit lower upper := by
      exact ⟨haUmin, Or.inl ⟨haLower, huminUpper⟩⟩
    let target : ParentCrossingGap lower upper :=
      ⟨span, mem_parentCrossingGaps_iff.mpr ⟨hadj, hcross⟩⟩
    refine ⟨target, ?_⟩
    constructor
    · intro hrightLower
      exact (Finset.disjoint_left.mp hdisjoint hrightLower
        (by simpa [target, span] using huminUpper)).elim
    · intro _
      rintro ⟨x, hxUpper, hxa⟩
      have hxMin : umin ≤ x := Finset.min'_le upper x hxUpper
      have : x < umin := hxa.trans haUmin
      exact (not_lt_of_ge hxMin) this
  · let before := upper.filter fun a => a < lmin
    have hbefore : before.Nonempty :=
      ⟨umin, Finset.mem_filter.mpr ⟨huminUpper, hul⟩⟩
    let a := before.max' hbefore
    have haBefore : a ∈ before := Finset.max'_mem before hbefore
    have haData := Finset.mem_filter.mp haBefore
    have haUpper : a ∈ upper := haData.1
    have haLmin : a < lmin := haData.2
    let span : SweepSpanEndpoints n := ⟨a, lmin⟩
    have hadj : span.IsAdjacentIn (lower ∪ upper) := by
      refine ⟨haLmin, Finset.mem_union_right lower haUpper,
        Finset.mem_union_left upper hlminLower, ?_⟩
      intro x hxSupport hxInside
      have hax : a < x := by simpa [span] using hxInside.1
      have hxLmin : x < lmin := by simpa [span] using hxInside.2
      rcases Finset.mem_union.mp hxSupport with hxLower | hxUpper
      · exact (not_lt_of_ge (Finset.min'_le lower x hxLower)) hxLmin
      · have hxBefore : x ∈ before :=
          Finset.mem_filter.mpr ⟨hxUpper, hxLmin⟩
        exact (not_lt_of_ge (Finset.le_max' before x hxBefore)) hax
    have hcross : span.CrossesSplit lower upper := by
      exact ⟨haLmin, Or.inr ⟨haUpper, hlminLower⟩⟩
    let target : ParentCrossingGap lower upper :=
      ⟨span, mem_parentCrossingGaps_iff.mpr ⟨hadj, hcross⟩⟩
    refine ⟨target, ?_⟩
    constructor
    · intro _
      rintro ⟨x, hxLower, hxa⟩
      have hxMin : lmin ≤ x := Finset.min'_le lower x hxLower
      have : x < lmin := hxa.trans haLmin
      exact (not_lt_of_ge hxMin) this
    · intro hrightUpper
      exact (Finset.disjoint_left.mp hdisjoint
        (by simpa [target, span] using hlminLower) hrightUpper).elim

/-- A nonempty disjoint binary merge has exactly one initial crossing. -/
theorem existsUnique_initialParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper) :
    ∃! target : ParentCrossingGap lower upper,
      IsInitialParentCrossingGap lower upper target.1 := by
  obtain ⟨target, htarget⟩ :=
    exists_initialParentCrossingGap hlower hupper hdisjoint
  refine ⟨target, htarget, ?_⟩
  intro other hother
  have heq : target.1 = other.1 :=
    IsInitialParentCrossingGap.eq (first := target.1) (second := other.1)
      hdisjoint
    (mem_parentCrossingGaps_iff.mp target.2)
    (mem_parentCrossingGaps_iff.mp other.2) htarget hother
  exact Subtype.ext heq.symm

/-- Every noninitial parent crossing lies in the image of the canonical
all-hidden-source matching. The remaining exact `+1` statement is reduced to
existence and uniqueness of an initial crossing. -/
theorem ParentCrossingGap.exists_allHiddenSource_of_not_initial
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper) (target : ParentCrossingGap lower upper)
    (hnotInitial : ¬IsInitialParentCrossingGap lower upper target.1) :
    ∃ source : AllHiddenGapSource lower upper,
      allHiddenGapSourceEntering source = target := by
  have htarget := mem_parentCrossingGaps_iff.mp target.2
  rcases htarget.2.2 with hsides | hsides
  · have hprior : ∃ a ∈ upper, a < target.1.left := by
      by_contra hnoPrior
      apply hnotInitial
      constructor
      · intro hrightLower
        exact (Finset.disjoint_left.mp hdisjoint hrightLower hsides.2).elim
      · intro _
        exact hnoPrior
    obtain ⟨source, hsource⟩ :=
      htarget.exists_hiddenUpperSource_of_prior_upper
        hdisjoint hsides hprior
    refine ⟨Sum.inl source, ?_⟩
    apply Subtype.ext
    exact hsource
  · have hprior : ∃ a ∈ lower, a < target.1.left := by
      by_contra hnoPrior
      apply hnotInitial
      constructor
      · intro _
        exact hnoPrior
      · intro hrightUpper
        exact (Finset.disjoint_left.mp hdisjoint hsides.2 hrightUpper).elim
    obtain ⟨source, hsource⟩ :=
      htarget.exists_hiddenLowerSource_of_prior_lower
        hdisjoint hsides hprior
    refine ⟨Sum.inr source, ?_⟩
    apply Subtype.ext
    exact hsource

/-- A canonical entering transition is never initial: its source left endpoint
is an earlier vertex in the child entered on the right. -/
theorem allHiddenGapSourceEntering_not_initial
    {n : ℕ} {lower upper : Finset (Fin n)}
    (source : AllHiddenGapSource lower upper) :
    ¬IsInitialParentCrossingGap lower upper
      (allHiddenGapSourceEntering source).1 := by
  intro hinitial
  cases source with
  | inl source =>
      have hsource := mem_hiddenGapSources_iff.mp source.2
      apply hinitial.2
        (by simpa [allHiddenGapSourceEntering,
          source.enteringParentCrossingGap_right] using hsource.1.2.2.1)
      exact ⟨source.1.left, hsource.1.2.1,
        source.left_lt_enteringParentCrossingGap_left⟩
  | inr source =>
      have hsource := mem_hiddenGapSources_iff.mp source.2
      apply hinitial.1
        (by simpa [allHiddenGapSourceEntering,
          source.enteringParentCrossingGap_right] using hsource.1.2.2.1)
      exact ⟨source.1.left, hsource.1.2.1,
        source.left_lt_enteringParentCrossingGap_left⟩

/-- The canonical matching hits exactly the noninitial parent crossings. -/
theorem exists_allHiddenGapSource_iff_not_initial
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper)
    (target : ParentCrossingGap lower upper) :
    (∃ source : AllHiddenGapSource lower upper,
      allHiddenGapSourceEntering source = target) ↔
      ¬IsInitialParentCrossingGap lower upper target.1 := by
  constructor
  · rintro ⟨source, rfl⟩
    exact allHiddenGapSourceEntering_not_initial source
  · exact target.exists_allHiddenSource_of_not_initial hdisjoint

/-- The canonical matching is an equivalence between all hidden child gaps
and the noninitial parent crossing transitions. -/
noncomputable def allHiddenGapSourceEquivNoninitialParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hdisjoint : Disjoint lower upper) :
    AllHiddenGapSource lower upper ≃
      {target : ParentCrossingGap lower upper //
        ¬IsInitialParentCrossingGap lower upper target.1} := by
  classical
  let preimage :
      {target : ParentCrossingGap lower upper //
        ¬IsInitialParentCrossingGap lower upper target.1} →
        AllHiddenGapSource lower upper := fun target =>
    Classical.choose
      ((exists_allHiddenGapSource_iff_not_initial hdisjoint target.1).mpr
        target.2)
  refine
    { toFun := fun source =>
        ⟨allHiddenGapSourceEntering source,
          allHiddenGapSourceEntering_not_initial source⟩
      invFun := preimage
      left_inv := ?_
      right_inv := ?_ }
  · intro source
    apply allHiddenGapSourceEntering_injective hdisjoint
    exact (Classical.choose_spec
      ((exists_allHiddenGapSource_iff_not_initial hdisjoint
        (allHiddenGapSourceEntering source)).mpr
          (allHiddenGapSourceEntering_not_initial source)))
  · intro target
    apply Subtype.ext
    exact (Classical.choose_spec
      ((exists_allHiddenGapSource_iff_not_initial hdisjoint target.1).mpr
        target.2))

/-- Exact finite genealogy of a nonempty disjoint merge: every parent
crossing is either the unique initial crossing or the canonical entering
transition of exactly one hidden child gap. -/
noncomputable def allHiddenGapSourceSumUnitEquivParentCrossingGap
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper) :
    AllHiddenGapSource lower upper ⊕ Unit ≃
      ParentCrossingGap lower upper := by
  classical
  let initial : ParentCrossingGap lower upper :=
    Classical.choose
      (exists_initialParentCrossingGap hlower hupper hdisjoint)
  have hinitial : IsInitialParentCrossingGap lower upper initial.1 :=
    Classical.choose_spec
      (exists_initialParentCrossingGap hlower hupper hdisjoint)
  letI : Unique
      {target : ParentCrossingGap lower upper //
        IsInitialParentCrossingGap lower upper target.1} :=
    { default := ⟨initial, hinitial⟩
      uniq := by
        intro target
        apply Subtype.ext
        apply Subtype.ext
        exact IsInitialParentCrossingGap.eq
          (first := target.1.1) (second := initial.1)
          hdisjoint
          (mem_parentCrossingGaps_iff.mp target.1.2)
          (mem_parentCrossingGaps_iff.mp initial.2)
          target.2 hinitial }
  exact
    (((allHiddenGapSourceEquivNoninitialParentCrossingGap hdisjoint).sumCongr
      (Equiv.ofUnique Unit
        {target : ParentCrossingGap lower upper //
          IsInitialParentCrossingGap lower upper target.1})).trans
      (Equiv.sumComm _ _)).trans
      (Equiv.sumCompl fun target : ParentCrossingGap lower upper =>
        IsInitialParentCrossingGap lower upper target.1)

/-- Cardinal form of the exact genealogy identity. -/
theorem parentCrossingGap_card_eq_allHiddenGapSource_card_add_one
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper) :
    Fintype.card (ParentCrossingGap lower upper) =
      Fintype.card (AllHiddenGapSource lower upper) + 1 := by
  rw [← Fintype.card_congr
    (allHiddenGapSourceSumUnitEquivParentCrossingGap
      hlower hupper hdisjoint)]
  simp

/-- The parent transitions removed from rank two for one fixed color: the
image of that color's compatible hidden gaps under the canonical entering
map. -/
noncomputable def compatibleHiddenEnteringGaps
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    Finset (ParentCrossingGap lower upper) :=
  Finset.univ.map (hiddenGapSourceEnteringEmbedding lower upper color)

@[simp] theorem compatibleHiddenEnteringGaps_card
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    (compatibleHiddenEnteringGaps lower upper color).card =
      Fintype.card (HiddenGapSource lower upper color) := by
  classical
  simp [compatibleHiddenEnteringGaps]

/-- The fixed-color rank-two residual after compatible transitions have been
promoted to their exact ambient ranks. -/
noncomputable def rankTwoResidualCrossingGaps
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    Finset (ParentCrossingGap lower upper) :=
  Finset.univ \ compatibleHiddenEnteringGaps lower upper color

/-- Removing the compatible image at rank two and retaining it for promotion
is exactly cardinality preserving. -/
theorem rankTwoResidual_card_add_compatibleHidden_card_eq_parent
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    (rankTwoResidualCrossingGaps lower upper color).card +
      Fintype.card (HiddenGapSource lower upper color) =
        Fintype.card (ParentCrossingGap lower upper) := by
  classical
  change ((Finset.univ : Finset (ParentCrossingGap lower upper)) \
      compatibleHiddenEnteringGaps lower upper color).card +
        Fintype.card (HiddenGapSource lower upper color) = _
  rw [← compatibleHiddenEnteringGaps_card, ← Finset.card_univ]
  exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)

/-- After promoting one color, the residual rank-two transitions are exactly
one initial transition plus the hidden sources of the opposite color, at the
level of cardinality. This is the fixed-color arithmetic used by the bounded
promotion census. -/
theorem rankTwoResidual_card_eq_complementHidden_card_add_one
    {n : ℕ} {lower upper : Finset (Fin n)}
    (hlower : lower.Nonempty) (hupper : upper.Nonempty)
    (hdisjoint : Disjoint lower upper) (color : Turn) :
    (rankTwoResidualCrossingGaps lower upper color).card =
      Fintype.card (HiddenGapSource lower upper color.complement) + 1 := by
  have htotal := parentCrossingGap_card_eq_allHiddenGapSource_card_add_one
    hlower hupper hdisjoint
  have hfixed :=
    rankTwoResidual_card_add_compatibleHidden_card_eq_parent
      lower upper color
  rw [Fintype.card_sum] at htotal
  cases color with
  | left =>
      change (rankTwoResidualCrossingGaps lower upper .left).card =
        Fintype.card (HiddenGapSource lower upper .right) + 1
      change (rankTwoResidualCrossingGaps lower upper .left).card +
        Fintype.card (HiddenGapSource lower upper .left) =
          Fintype.card (ParentCrossingGap lower upper) at hfixed
      omega
  | right =>
      change (rankTwoResidualCrossingGaps lower upper .right).card =
        Fintype.card (HiddenGapSource lower upper .left) + 1
      change (rankTwoResidualCrossingGaps lower upper .right).card +
        Fintype.card (HiddenGapSource lower upper .right) =
          Fintype.card (ParentCrossingGap lower upper) at hfixed
      omega

/-- A promoted hidden gap with its exact rank in the parent ambient support.
This carrier deliberately has no crossing field: both endpoints remain in one
child at the parent node. -/
structure AmbientGapPromotion {n : ℕ} (color : Turn)
    (chi : TripleColoring n) (lower upper : Finset (Fin n))
    (span : SweepSpanEndpoints n) where
  rank : ℕ
  three_le_rank : 3 ≤ rank
  exact_rank : HasExactSpanRank color chi (lower ∪ upper) span rank

/-- The new ambient-support carrier selected by the gap-promotion gate. Its
source is color-compatible and its exact rank lives in the parent support;
it intentionally carries no crossing assertion. -/
structure AmbientPromotedGap {n : ℕ} (color : Turn)
    (chi : TripleColoring n) (lower upper : Finset (Fin n)) where
  span : SweepSpanEndpoints n
  source : span ∈ hiddenGapSources lower upper color
  rank : ℕ
  three_le_rank : 3 ≤ rank
  exact_rank : HasExactSpanRank color chi (lower ∪ upper) span rank

private theorem isCapSet_ordered_three {n : ℕ} {chi : TripleColoring n}
    {a q b : Fin n} (haq : a < q) (hqb : q < b)
    (hcolor : chi ⟨a, q, b, haq, hqb⟩ = .right) :
    IsCapSet chi {a, q, b} := by
  rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
  rcases hi with rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> try omega

private theorem isCupSet_ordered_three {n : ℕ} {chi : TripleColoring n}
    {a q b : Fin n} (haq : a < q) (hqb : q < b)
    (hcolor : chi ⟨a, q, b, haq, hqb⟩ = .left) :
    IsCupSet chi {a, q, b} := by
  rintro ⟨i, j, k, hij, hjk⟩ hi hj hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hk
  rcases hi with rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;> try omega

private theorem hasSweepSpan_ordered_three {n : ℕ} {a q b : Fin n}
    (haq : a < q) (hqb : q < b) : HasSweepSpan {a, q, b} a b := by
  refine ⟨haq.trans hqb, by simp, by simp, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> omega

/-- A hidden lower-child gap supplies a genuine parent cap of rank at least
three with the same two endpoints. -/
theorem IsHiddenLowerGap.hasCapSpanRankAtLeast_three
    {n : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hgap : IsHiddenLowerGap lower upper span) :
    HasCapSpanRankAtLeast chi (lower ∪ upper) span.left span.right 3 := by
  obtain ⟨hadj, q, hqUpper, hleftq, hqright⟩ := hgap
  have hleftLower := hadj.2.1
  have hrightLower := hadj.2.2.1
  have hdisjoint := Finset.disjoint_left.mp hdeep.disjoint
  have hqNotLower : q ∉ lower := fun hqLower => hdisjoint hqLower hqUpper
  have hleftNotUpper : span.left ∉ upper :=
    fun hleftUpper => hdisjoint hleftLower hleftUpper
  let triple : OrderedTriple n :=
    ⟨span.left, q, span.right, hleftq, hqright⟩
  have hcolor : chi triple = .right := by
    have hcross := hdeep.crossing triple
      (Finset.mem_union_left upper hleftLower)
      (Finset.mem_union_right lower hqUpper)
      (Finset.mem_union_left upper hrightLower)
      (by
        rintro ⟨_, hqLower, _⟩
        exact hqNotLower (by simpa [triple] using hqLower))
      (by
        rintro ⟨hleftUpper, _, _⟩
        exact hleftNotUpper (by simpa [triple] using hleftUpper))
    simpa [triple, hqNotLower] using hcross
  refine ⟨{span.left, q, span.right}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_left upper hleftLower
    · exact Finset.mem_union_right lower hqUpper
    · exact Finset.mem_union_left upper hrightLower
  · simp [hleftq.ne, hqright.ne, (hleftq.trans hqright).ne]
  · exact isCapSet_ordered_three hleftq hqright hcolor
  · exact hasSweepSpan_ordered_three hleftq hqright

/-- A hidden upper-child gap supplies a genuine parent cup of rank at least
three with the same two endpoints. -/
theorem IsHiddenUpperGap.hasCupSpanRankAtLeast_three
    {n : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hgap : IsHiddenUpperGap lower upper span) :
    HasCupSpanRankAtLeast chi (lower ∪ upper) span.left span.right 3 := by
  obtain ⟨hadj, q, hqLower, hleftq, hqright⟩ := hgap
  have hleftUpper := hadj.2.1
  have hrightUpper := hadj.2.2.1
  have hdisjoint := Finset.disjoint_left.mp hdeep.disjoint
  have hqNotUpper : q ∉ upper := fun hqUpper => hdisjoint hqLower hqUpper
  have hleftNotLower : span.left ∉ lower :=
    fun hleftLower => hdisjoint hleftLower hleftUpper
  let triple : OrderedTriple n :=
    ⟨span.left, q, span.right, hleftq, hqright⟩
  have hcolor : chi triple = .left := by
    have hcross := hdeep.crossing triple
      (Finset.mem_union_right lower hleftUpper)
      (Finset.mem_union_left upper hqLower)
      (Finset.mem_union_right lower hrightUpper)
      (by
        rintro ⟨hleftLower, _, _⟩
        exact hleftNotLower (by simpa [triple] using hleftLower))
      (by
        rintro ⟨_, hqUpper, _⟩
        exact hqNotUpper (by simpa [triple] using hqUpper))
    simpa [triple, hqLower] using hcross
  refine ⟨{span.left, q, span.right}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_right lower hleftUpper
    · exact Finset.mem_union_left upper hqLower
    · exact Finset.mem_union_right lower hrightUpper
  · simp [hleftq.ne, hqright.ne, (hleftq.trans hqright).ne]
  · exact isCupSet_ordered_three hleftq hqright hcolor
  · exact hasSweepSpan_ordered_three hleftq hqright

/-- Every hidden lower gap has an exact-rank cap promotion object in the
parent support. -/
theorem IsHiddenLowerGap.exists_ambientGapPromotion
    {n : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hgap : IsHiddenLowerGap lower upper span) :
    Nonempty (AmbientGapPromotion .right chi lower upper span) := by
  have hthree : HasSpanRankAtLeast .right chi (lower ∪ upper) span 3 :=
    hgap.hasCapSpanRankAtLeast_three hdeep
  obtain ⟨rank, hthree, hexact⟩ :=
    HasSpanRankAtLeast.exists_exact_rank_at_least hthree
  exact ⟨⟨rank, hthree, hexact⟩⟩

/-- Every hidden upper gap has an exact-rank cup promotion object in the
parent support. -/
theorem IsHiddenUpperGap.exists_ambientGapPromotion
    {n : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {span : SweepSpanEndpoints n} (hdeep : HasDeepBelowSplit chi lower upper)
    (hgap : IsHiddenUpperGap lower upper span) :
    Nonempty (AmbientGapPromotion .left chi lower upper span) := by
  have hthree : HasSpanRankAtLeast .left chi (lower ∪ upper) span 3 :=
    hgap.hasCupSpanRankAtLeast_three hdeep
  obtain ⟨rank, hthree, hexact⟩ :=
    HasSpanRankAtLeast.exists_exact_rank_at_least hthree
  exact ⟨⟨rank, hthree, hexact⟩⟩

/-- Every color-compatible source gap lifts to the explicit exact-rank
ambient carrier. -/
theorem exists_ambientPromotedGap_of_mem
    {n : ℕ} {chi : TripleColoring n} {lower upper : Finset (Fin n)}
    {color : Turn} {span : SweepSpanEndpoints n}
    (hdeep : HasDeepBelowSplit chi lower upper)
    (hsource : span ∈ hiddenGapSources lower upper color) :
    ∃ promoted : AmbientPromotedGap color chi lower upper,
      promoted.span = span := by
  rw [mem_hiddenGapSources_iff] at hsource
  cases color with
  | left =>
      obtain ⟨promotion⟩ := hsource.exists_ambientGapPromotion hdeep
      exact ⟨⟨span, by simpa [hiddenGapSources], promotion.rank,
        promotion.three_le_rank, promotion.exact_rank⟩, rfl⟩
  | right =>
      obtain ⟨promotion⟩ := hsource.exists_ambientGapPromotion hdeep
      exact ⟨⟨span, by simpa [hiddenGapSources], promotion.rank,
        promotion.three_le_rank, promotion.exact_rank⟩, rfl⟩

/-- Color-compatible hidden sources whose promoted parent-support rank is
exactly the specified rank. This is the fixed-rank family used by the bounded
adjusted-demand gate. -/
noncomputable def promotedExactRankSources
    {n : ℕ} (color : Turn) (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (rank : ℕ) :
    Finset (SweepSpanEndpoints n) := by
  classical
  exact (hiddenGapSources lower upper color).filter fun span =>
    HasExactSpanRank color chi (lower ∪ upper) span rank

@[simp] theorem mem_promotedExactRankSources
    {n rank : ℕ} {color : Turn} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)} {span : SweepSpanEndpoints n} :
    span ∈ promotedExactRankSources color chi lower upper rank ↔
      span ∈ hiddenGapSources lower upper color ∧
        HasExactSpanRank color chi (lower ∪ upper) span rank := by
  classical
  simp [promotedExactRankSources]

abbrev PromotedExactRankSource
    {n : ℕ} (color : Turn) (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) (rank : ℕ) :=
  {span // span ∈ promotedExactRankSources color chi lower upper rank}

/-- A fixed-rank source is the proof-irrelevant finite presentation of an
ambient promoted object. -/
def PromotedExactRankSource.toAmbientPromotedGap
    {n rank : ℕ} {color : Turn} {chi : TripleColoring n}
    {lower upper : Finset (Fin n)}
    (source : PromotedExactRankSource color chi lower upper rank)
    (hthree : 3 ≤ rank) : AmbientPromotedGap color chi lower upper := by
  have hsource := mem_promotedExactRankSources.mp source.2
  exact ⟨source.1, hsource.1, rank, hthree, hsource.2⟩

namespace AmbientPromotedGap

variable {n k : ℕ} {chi : TripleColoring n}
  {lower upper : Finset (Fin n)} {color : Turn}

/-- A promoted exact ambient rank remains below the forbidden strong-set size
in an open parent context. -/
theorem rank_lt (promoted : AmbientPromotedGap color chi lower upper)
    (hnoStrong : ¬ContainsStrongPolygonSet chi (lower ∪ upper) k) :
    promoted.rank < k :=
  promoted.exact_rank.lt_of_not_containsStrongPolygonSet hnoStrong

/-- The actual parent-support endpoint-rank profiles for a promoted gap. -/
def endpointRankTransitionProfiles
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k) :
    AllocatedEndpointTransitionProfiles chi lower upper color promoted.rank k
      (PascalGridIdeal (promoted.rank - 1)
        (k - promoted.rank - 1)) :=
  allocatedEndpointRankTransitionProfiles (rank := promoted.rank) (k := k)
    chi lower upper color
    (by exact (by omega : 1 ≤ 3).trans promoted.three_le_rank) hrankTop

/-- The endpoint-rank candidate family used by the bounded gate, generalized
to the promoted noncrossing carrier. Its ideals are computed in the same
parent ambient support as `promoted.exact_rank`. -/
def endpointRankTransitionCandidates
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k) :
    Finset (PascalGridIdeal (promoted.rank - 1)
      (k - promoted.rank - 1)) :=
  endpointTransitionCandidatesForSpan
    (promoted.endpointRankTransitionProfiles k hrankTop) promoted.span

/-- The generalized candidate family is nonempty without a crossing premise,
Hall premise, or capacity assumption. -/
theorem endpointRankTransitionCandidates_nonempty
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k) :
    (promoted.endpointRankTransitionCandidates k hrankTop).Nonempty := by
  exact endpointTransitionCandidatesForSpan_nonempty _ _

/-- When one complementary-rank column remains, an exact promoted span
defines the extreme same-color cell `(rank - 2, 0)` of its rank rectangle. -/
def sameColorCorner
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankInterior : promoted.rank + 1 < k) :
    Fin (promoted.rank - 1) × Fin (k - promoted.rank - 1) :=
  (⟨promoted.rank - 2, by
      have := promoted.three_le_rank
      omega⟩,
    ⟨0, by
      have := hrankInterior
      omega⟩)

/-- The promoted span itself places its same-color corner in the future
profile at its left endpoint. This is the first noncrossing incidence fact:
it uses exact ambient rank, not a crossing-ray normal form. -/
theorem sameColorCorner_mem_future_left
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k)
    (hrankInterior : promoted.rank + 1 < k) :
    promoted.sameColorCorner k hrankInterior ∈
      (promoted.endpointRankTransitionProfiles k hrankTop).future
        promoted.span.left := by
  classical
  change promoted.sameColorCorner k hrankInterior ∈
    (endpointFutureRankIdeal chi (lower ∪ upper) color promoted.rank k
      promoted.span.left).cells
  simp only [endpointFutureRankIdeal]
  rw [Finset.mem_filter]
  have hdata := promoted.exact_rank.1.ordered_endpoints_mem
  have hcomplement :
      HasSpanRankAtLeast color.complement chi (lower ∪ upper)
        promoted.span 2 :=
    HasSpanRankAtLeast.two_of_lt_mem hdata.1 hdata.2.1 hdata.2.2
  refine ⟨Finset.mem_univ _, promoted.span.right, hdata.2.2, hdata.1,
    ?_, ?_⟩
  · have hrank : promoted.rank - 2 + 2 = promoted.rank := by
      have := promoted.three_le_rank
      omega
    simpa [sameColorCorner, hrank] using promoted.exact_rank.1
  · simpa [sameColorCorner] using hcomplement

/-- Dually, the same-color corner lies in the past profile at the promoted
span's right endpoint. -/
theorem sameColorCorner_mem_past_right
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k)
    (hrankInterior : promoted.rank + 1 < k) :
    promoted.sameColorCorner k hrankInterior ∈
      (promoted.endpointRankTransitionProfiles k hrankTop).past
        promoted.span.right := by
  classical
  change promoted.sameColorCorner k hrankInterior ∈
    (endpointPastRankIdeal chi (lower ∪ upper) color promoted.rank k
      promoted.span.right).cells
  simp only [endpointPastRankIdeal]
  rw [Finset.mem_filter]
  have hdata := promoted.exact_rank.1.ordered_endpoints_mem
  have hcomplement :
      HasSpanRankAtLeast color.complement chi (lower ∪ upper)
        promoted.span 2 :=
    HasSpanRankAtLeast.two_of_lt_mem hdata.1 hdata.2.1 hdata.2.2
  refine ⟨Finset.mem_univ _, promoted.span.left, hdata.2.1, hdata.1,
    ?_, ?_⟩
  · have hrank : promoted.rank - 2 + 2 = promoted.rank := by
      have := promoted.three_le_rank
      omega
    simpa [sameColorCorner, hrank] using promoted.exact_rank.1
  · simpa [sameColorCorner] using hcomplement

/-- The two profile states whose incidence is certified above are members of
the promoted span's endpoint-candidate family. -/
theorem endpointRankTransitionCandidates_contains_incident_profiles
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k) :
    (promoted.endpointRankTransitionProfiles k hrankTop).future
          promoted.span.left ∈
        promoted.endpointRankTransitionCandidates k hrankTop ∧
      (promoted.endpointRankTransitionProfiles k hrankTop).past
          promoted.span.right ∈
        promoted.endpointRankTransitionCandidates k hrankTop := by
  exact ⟨endpointTransitionCandidatesForSpan_future_left_mem _ _,
    endpointTransitionCandidatesForSpan_past_right_mem _ _⟩

/-- Candidate ideals mapped into the exact Pascal layer used by the bounded
promotion gate. -/
def endpointPascalSlotCandidates
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k) :
    Finset (AllocatedPascalSlot promoted.rank k) :=
  (promoted.endpointRankTransitionCandidates k hrankTop).map
    (promoted.endpointRankTransitionProfiles k hrankTop).encode

theorem endpointPascalSlotCandidates_nonempty
    (promoted : AmbientPromotedGap color chi lower upper) (k : ℕ)
    (hrankTop : promoted.rank < k) :
    (promoted.endpointPascalSlotCandidates k hrankTop).Nonempty := by
  obtain ⟨ideal, hideal⟩ :=
    promoted.endpointRankTransitionCandidates_nonempty k hrankTop
  refine ⟨(promoted.endpointRankTransitionProfiles k hrankTop).encode ideal, ?_⟩
  exact Finset.mem_map.mpr ⟨ideal, hideal, rfl⟩

end AmbientPromotedGap

/-- The finite fixed-color demand retained at rank two after compatible
hidden gaps are promoted. -/
abbrev AdjustedRankTwoDemand {n : ℕ}
    (lower upper : Finset (Fin n)) (color : Turn) :=
  {target // target ∈ rankTwoResidualCrossingGaps lower upper color}

@[simp] theorem adjustedRankTwoDemand_card
    {n : ℕ} (lower upper : Finset (Fin n)) (color : Turn) :
    Fintype.card (AdjustedRankTwoDemand lower upper color) =
      (rankTwoResidualCrossingGaps lower upper color).card := by
  exact Fintype.card_coe _

/-- At every higher rank, the adjusted demand is the disjoint sum of the
existing minimal crossing frontier and the new noncrossing promoted sources.
The sum records proof obligations, not merely distinct endpoint pairs. -/
abbrev AdjustedHigherRankDemand {n rank : ℕ}
    (color : Turn) (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) :=
  {span // span ∈ allocatedExactRankFrontier chi lower upper color rank} ⊕
    PromotedExactRankSource color chi lower upper rank

@[simp] theorem adjustedHigherRankDemand_card
    {n rank : ℕ} (color : Turn) (chi : TripleColoring n)
    (lower upper : Finset (Fin n)) :
    Fintype.card (AdjustedHigherRankDemand (rank := rank)
      color chi lower upper) =
      (allocatedExactRankFrontier chi lower upper color rank).card +
        (promotedExactRankSources color chi lower upper rank).card := by
  simp [AdjustedHigherRankDemand]

namespace AdjustedHigherRankDemand

variable {n rank k : ℕ} {chi : TripleColoring n}
  {lower upper : Finset (Fin n)} {color : Turn}

/-- Forget whether an adjusted higher-rank demand came from the crossing
frontier or from a promoted hidden source. -/
def span (demand : AdjustedHigherRankDemand (rank := rank)
    color chi lower upper) : SweepSpanEndpoints n :=
  match demand with
  | .inl crossing => crossing.1
  | .inr promoted => promoted.1

/-- Both summands have the same exact rank in the same parent support. -/
theorem exact_rank (demand : AdjustedHigherRankDemand (rank := rank)
    color chi lower upper) :
    HasExactSpanRank color chi (lower ∪ upper) demand.span rank := by
  cases demand with
  | inl crossing =>
      exact (mem_allocatedExactRankSpans.mp
        (mem_allocatedExactRankFrontier.mp crossing.2).1).2
  | inr promoted =>
      exact (mem_promotedExactRankSources.mp promoted.2).2

/-- The shared parent-support endpoint-rank profiles for the adjusted demand
at one higher rank. -/
def endpointRankTransitionProfiles
    (hrank : 1 ≤ rank) (hrankTop : rank < k) :
    AllocatedEndpointTransitionProfiles chi lower upper color rank k
      (PascalGridIdeal (rank - 1) (k - rank - 1)) :=
  allocatedEndpointRankTransitionProfiles (rank := rank) (k := k)
    chi lower upper color hrank hrankTop

/-- Candidate ideals for either summand, using the common ambient span
interface rather than pretending promoted gaps cross the split. -/
def endpointRankTransitionCandidates
    (demand : AdjustedHigherRankDemand (rank := rank)
      color chi lower upper)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) :
    Finset (PascalGridIdeal (rank - 1) (k - rank - 1)) :=
  endpointTransitionCandidatesForSpan
    (endpointRankTransitionProfiles (chi := chi) (lower := lower)
      (upper := upper) (color := color) hrank hrankTop)
    demand.span

theorem endpointRankTransitionCandidates_nonempty
    (demand : AdjustedHigherRankDemand (rank := rank)
      color chi lower upper)
    (hrank : 1 ≤ rank) (hrankTop : rank < k) :
    (demand.endpointRankTransitionCandidates hrank hrankTop).Nonempty := by
  exact endpointTransitionCandidatesForSpan_nonempty _ _

/-- Hall expansion for the complete adjusted higher-rank carrier. This is now
the exact structural obstruction: it includes crossing frontier spans and
promoted noncrossing gaps in one family. -/
def EndpointRankTransitionHall
    (hrank : 1 ≤ rank) (hrankTop : rank < k) : Prop :=
  ∀ demands : Finset (AdjustedHigherRankDemand (rank := rank)
      color chi lower upper),
    demands.card ≤
      (demands.biUnion fun demand =>
        demand.endpointRankTransitionCandidates hrank hrankTop).card

/-- A distinct Pascal slot for every member of the adjusted higher-rank
demand. -/
structure Slotting (rank k : ℕ) where
  slot : AdjustedHigherRankDemand (rank := rank)
      color chi lower upper → AllocatedPascalSlot rank k
  injective : Function.Injective slot

/-- Hall expansion constructs the adjusted slotting, using the same boundary
encoding for both summands. -/
noncomputable def Slotting.of_endpointRankTransitionHall
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hhall : EndpointRankTransitionHall
      (chi := chi) (lower := lower) (upper := upper) (color := color)
      hrank hrankTop) :
    Slotting (chi := chi) (lower := lower) (upper := upper)
      (color := color) rank k := by
  let candidates := fun demand : AdjustedHigherRankDemand (rank := rank)
      color chi lower upper =>
    demand.endpointRankTransitionCandidates hrank hrankTop
  let matching :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective candidates).mp hhall
  let representative := Classical.choose matching
  have hinjective : Function.Injective representative :=
    (Classical.choose_spec matching).1
  let profiles := endpointRankTransitionProfiles
    (chi := chi) (lower := lower) (upper := upper) (color := color)
    hrank hrankTop
  exact {
    slot := fun demand => profiles.encode (representative demand)
    injective := profiles.encode.injective.comp hinjective
  }

/-- Consequently, proving adjusted Hall gives exactly the published Pascal
capacity at every higher rank. -/
theorem card_le_publishedSpanPascalDemand_of_endpointRankTransitionHall
    (hrank : 1 ≤ rank) (hrankTop : rank < k)
    (hhall : EndpointRankTransitionHall
      (chi := chi) (lower := lower) (upper := upper) (color := color)
      hrank hrankTop) :
    (allocatedExactRankFrontier chi lower upper color rank).card +
        (promotedExactRankSources color chi lower upper rank).card ≤
      publishedSpanPascalDemand k rank := by
  let slotting := Slotting.of_endpointRankTransitionHall
    (chi := chi) (lower := lower) (upper := upper) (color := color)
    hrank hrankTop hhall
  have hcard := Fintype.card_le_of_injective slotting.slot slotting.injective
  rw [adjustedHigherRankDemand_card, Fintype.card_finset_len] at hcard
  simpa [publishedSpanPascalDemand] using hcard

end AdjustedHigherRankDemand

end


end ErdosSzekeres

end
