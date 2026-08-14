module

public import ErdosSzekeres.TothValtrCapExtension

@[expose] public section

/-!
# Convexity transfer from orientation signs

The Tóth--Valtr transformation is not affine, so the existing linear-equivalence
bridge does not apply.  This file proves the finite replacement actually
needed here: an injective map preserving both nonzero orientation signs on a
general-position set preserves the project's convex-position predicate.
-/

namespace ErdosSzekeres

noncomputable section

/-- A map preserves the two strict orientation signs on a finite set. -/
def PreservesOrientationSignsOn
    (f : Point 2 → Point 2) (s : Finset (Point 2)) : Prop :=
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ∀ ⦃c⦄, c ∈ s →
    (0 < orientation (f a) (f b) (f c) ↔ 0 < orientation a b c) ∧
    (orientation (f a) (f b) (f c) < 0 ↔ orientation a b c < 0)

private theorem insideTriangleBySigns_map_iff
    {f : Point 2 → Point 2} {s : Finset (Point 2)}
    (hsign : PreservesOrientationSignsOn f s)
    {a b c p : Point 2} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hp : p ∈ s) :
    InsideTriangleBySigns (f a) (f b) (f c) (f p) ↔
      InsideTriangleBySigns a b c p := by
  simp only [InsideTriangleBySigns]
  rw [(hsign ha hb hc).1, (hsign ha hb hp).1,
    (hsign hb hc hp).1, (hsign hc ha hp).1,
    (hsign ha hb hc).2, (hsign ha hb hp).2,
    (hsign hb hc hp).2, (hsign hc ha hp).2]

/-- Orientation-sign preservation carries general position to the image. -/
theorem InGeneralPosition.image_of_preservesOrientationSignsOn
    {s : Finset (Point 2)} {f : Point 2 → Point 2}
    (hgp : InGeneralPosition s) (hsign : PreservesOrientationSignsOn f s) :
    InGeneralPosition (s.image f) := by
  intro x hx y hy z hz hxy hxz hyz
  simp only [Finset.mem_image] at hx hy hz
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  obtain ⟨c, hc, rfl⟩ := hz
  have hab : a ≠ b := fun h => hxy (congrArg f h)
  have hac : a ≠ c := fun h => hxz (congrArg f h)
  have hbc : b ≠ c := fun h => hyz (congrArg f h)
  have horientation := hgp ha hb hc hab hac hbc
  rcases lt_or_gt_of_ne horientation with hneg | hpos
  · exact ne_of_lt ((hsign ha hb hc).2.mpr hneg)
  · exact ne_of_gt ((hsign ha hb hc).1.mpr hpos)

private theorem inConvexPosition_image_four_iff
    {s : Finset (Point 2)} {f : Point 2 → Point 2}
    (hgp : InGeneralPosition s) (hinj : Set.InjOn f s)
    (hsign : PreservesOrientationSignsOn f s)
    {a b c d : Point 2} (ha : a ∈ s) (hb : b ∈ s)
    (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    InConvexPosition {f a, f b, f c, f d} ↔
      InConvexPosition {a, b, c, d} := by
  have hsub : ({a, b, c, d} : Finset (Point 2)) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hgpSource : InGeneralPosition ({a, b, c, d} : Finset (Point 2)) :=
    hgp.mono hsub
  have hgpTarget : InGeneralPosition
      (({a, b, c, d} : Finset (Point 2)).image f) :=
    hgpSource.image_of_preservesOrientationSignsOn
      (fun _ hx _ hy _ hz => hsign (hsub hx) (hsub hy) (hsub hz))
  have htargetSet :
      (({a, b, c, d} : Finset (Point 2)).image f) = {f a, f b, f c, f d} := by
    simp
  rw [htargetSet] at hgpTarget
  rw [inConvexPosition_four_iff_orientation_signs
      (f a) (f b) (f c) (f d) hgpTarget
      (fun h => hab (hinj ha hb h))
      (fun h => hac (hinj ha hc h))
      (fun h => had (hinj ha hd h))
      (fun h => hbc (hinj hb hc h))
      (fun h => hbd (hinj hb hd h))
      (fun h => hcd (hinj hc hd h)),
    inConvexPosition_four_iff_orientation_signs
      a b c d hgpSource hab hac had hbc hbd hcd]
  rw [insideTriangleBySigns_map_iff hsign hb hc hd ha,
    insideTriangleBySigns_map_iff hsign ha hc hd hb,
    insideTriangleBySigns_map_iff hsign ha hb hd hc,
    insideTriangleBySigns_map_iff hsign ha hb hc hd]

/-- An injective orientation-sign equivalence on a finite general-position set
preserves convex position in both directions. -/
theorem inConvexPosition_image_iff_of_preservesOrientationSignsOn
    {s : Finset (Point 2)} {f : Point 2 → Point 2}
    (hgp : InGeneralPosition s) (hinj : Set.InjOn f s)
    (hsign : PreservesOrientationSignsOn f s) :
    InConvexPosition (s.image f) ↔ InConvexPosition s := by
  have himageGp := hgp.image_of_preservesOrientationSignsOn hsign
  have hfour : ∀ t : Finset (Point 2), t ⊆ s → t.card = 4 →
      (InConvexPosition (t.image f) ↔ InConvexPosition t) := by
    intro t hts htcard
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
      Finset.card_eq_four.mp htcard
    have ha : a ∈ s := hts (by simp)
    have hb : b ∈ s := hts (by simp)
    have hc : c ∈ s := hts (by simp)
    have hd : d ∈ s := hts (by simp)
    simpa using inConvexPosition_image_four_iff hgp hinj hsign
      ha hb hc hd hab hac had hbc hbd hcd
  constructor
  · intro himage
    apply (inConvexPosition_iff_four_subsets s hgp).2
    intro t hts htcard
    apply (hfour t hts htcard).mp
    apply himage.mono
    exact Finset.image_mono f hts
  · intro hs
    apply (inConvexPosition_iff_four_subsets (s.image f) himageGp).2
    intro u hus hucard
    obtain ⟨t, hts, rfl⟩ := Finset.subset_image_iff.mp hus
    have htcard : t.card = 4 := by
      rw [← hucard]
      exact (Finset.card_image_of_injOn (hinj.mono hts)).symm
    exact (hfour t hts htcard).mpr (hs.mono hts)

/-- The explicit Tóth--Valtr chart preserves convex position on every finite
set contained in its positive-denominator half-plane. -/
theorem inConvexPosition_image_tothValtrProjective_iff
    {s : Finset (Point 2)} (hgp : InGeneralPosition s)
    (δ : ℝ) (hδ : 0 < δ) (hhalf : ∀ p ∈ s, 0 < p 1 + δ) :
    InConvexPosition (s.image (tothValtrProjective δ)) ↔
      InConvexPosition s := by
  have hsign : PreservesOrientationSignsOn (tothValtrProjective δ) s := by
    intro a ha b hb c hc
    exact ⟨orientation_tothValtrProjective_pos_iff
        δ a b c hδ (hhalf a ha) (hhalf b hb) (hhalf c hc),
      orientation_tothValtrProjective_neg_iff
        δ a b c hδ (hhalf a ha) (hhalf b hb) (hhalf c hc)⟩
  have hinj : Set.InjOn (tothValtrProjective δ) s := by
    intro a ha b hb hab
    exact tothValtrProjective_injective_of_pos_denominators
      δ a b (ne_of_gt hδ) (hhalf a ha) (hhalf b hb) hab
  exact inConvexPosition_image_iff_of_preservesOrientationSignsOn hgp hinj hsign

end

end ErdosSzekeres

end
