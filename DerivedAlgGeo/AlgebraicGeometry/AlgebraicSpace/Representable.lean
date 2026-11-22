/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.AlgebraicSpace.FiberProduct
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.Etale

/-!
# Morphisms of presheaves representable by algebraic spaces

A morphism `a : F ⟶ G` of presheaves on `Over S` is representable by algebraic spaces
(Stacks 02YQ) when every base change `yoneda.obj U ×_G F` to a scheme `U` over `S` is an algebraic
space over `S`. For a property `P` of morphisms of schemes, `a` has `P` when moreover each base
change `yoneda.obj U ×_G F ⟶ yoneda.obj U` has `P` measured on an étale surjective atlas.

## Main definitions

* `AlgebraicGeometry.representableByAlgebraicSpaces S`: the morphisms of presheaves on `Over S`
  representable by algebraic spaces (Stacks 02YQ).
* `AlgebraicGeometry.representableByAlgebraicSpacesWith S P`: the morphisms representable by
  algebraic spaces whose base changes to schemes have `P` on some étale surjective atlas.

## Main results

* `representableByAlgebraicSpaces S` is stable under base change (Stacks 03Y0).
* `AlgebraicGeometry.relativelyRepresentable_le_representableByAlgebraicSpaces`: morphisms
  representable by schemes are representable by algebraic spaces.
* `AlgebraicGeometry.representableByAlgebraicSpaces_of_isAlgebraicSpace`: a morphism from an
  algebraic space to an fppf sheaf with representable diagonal is representable by algebraic
  spaces, and `AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces`: so is every
  morphism of algebraic spaces (Stacks 03BN).
* `AlgebraicGeometry.representableByAlgebraicSpacesWith_iff_forall`: for `P` that respects and
  descends along precomposition with étale surjections, one atlas suffices exactly when every
  atlas does (compare Stacks 03MJ).
* `representableByAlgebraicSpacesWith S P` is stable under base change (Stacks 046F), for every
  `P`.
* `AlgebraicGeometry.presheaf_le_representableByAlgebraicSpacesWith`: a morphism whose base
  changes to schemes have `P` is representable by algebraic spaces with `P`.

## Implementation notes

Two pullbacks must be kept apart. `Limits.pullback a ξ` is the pullback in the presheaf category
`(Over S)ᵒᵖ ⥤ Type u`; schemes enter only through `yoneda` and `Yoneda.fullyFaithful.preimage`,
and no scheme fibre product is formed.

Stacks 03XZ defines "`a` has `P`" for a property `P` of morphisms of algebraic spaces, through the
morphisms of algebraic spaces `yoneda.obj U ×_G F ⟶ yoneda.obj U`. Properties of morphisms of
algebraic spaces are not formalized here, so `representableByAlgebraicSpacesWith` measures a
property of morphisms of schemes on an étale surjective atlas, which is how Stacks 04RD defines
the property of morphisms of algebraic spaces induced by one étale local on the source-and-target.
Atlases are `(@Etale ⊓ @Surjective).over.presheaf`, as in `AlgebraicGeometry.isAlgebraicSpace`.

Atlas independence uses only `MorphismProperty.RespectsLeft` and
`MorphismProperty.HasOfPrecompProperty` with respect to `@Etale ⊓ @Surjective`: two atlases of one
base change are compared through their fibre product, a scheme étale and surjective over both.
Mathlib's `MorphismProperty.IsLocalAtSource` is not the right class, since it asks for `P` on
every member of a cover and `@Surjective` is not local in that sense. For `@Surjective` both
instances are available: `RespectsLeft` from `DerivedAlgGeo.AlgebraicGeometry.Morphisms.Etale`,
imported here, and `HasOfPrecompProperty` from Mathlib.

## References

* [Stacks, Section 80.3 (Tag 02YP)](https://stacks.math.columbia.edu/tag/02YP)
* [Stacks, Section 80.4 (Tag 046E)](https://stacks.math.columbia.edu/tag/046E)
* [Stacks, Section 67.22 (Tag 03MI)](https://stacks.math.columbia.edu/tag/03MI)

## Tags

algebraic space, representable by algebraic spaces, étale atlas, base change
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- A morphism `a : F ⟶ G` of presheaves on `Over S` is **representable by algebraic spaces**
(Stacks 02YQ) when its base change along every map `ξ : yoneda.obj U ⟶ G` from a scheme `U` over
`S` is an algebraic space over `S`. -/
def representableByAlgebraicSpaces : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  fun _ G a ↦ ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), isAlgebraicSpace S (pullback a ξ)

variable {S}

/-- A base change of a morphism representable by algebraic spaces to a scheme is an algebraic
space, whichever pullback square presents it. -/
theorem representableByAlgebraicSpaces.isAlgebraicSpace_of_isPullback
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G} (ha : representableByAlgebraicSpaces S a)
    {U : Over S} {ξ : yoneda.obj U ⟶ G} {X : (Over S)ᵒᵖ ⥤ Type u} {fst : X ⟶ F}
    {snd : X ⟶ yoneda.obj U} (h : IsPullback fst snd a ξ) : isAlgebraicSpace S X :=
  (isAlgebraicSpace S).prop_of_iso h.isoPullback.symm (ha ξ)

variable (S) in
/-- Morphisms representable by algebraic spaces are stable under base change (Stacks 03Y0). -/
instance : (representableByAlgebraicSpaces S).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ _ _ _ g'} sq hg _ ξ :=
    hg.isAlgebraicSpace_of_isPullback ((IsPullback.of_hasPullback g' ξ).paste_horiz sq)

variable (S) in
/-- A morphism representable by schemes is representable by algebraic spaces: its base changes to
schemes are schemes, and schemes are algebraic spaces (Stacks 025Z). -/
theorem relativelyRepresentable_le_representableByAlgebraicSpaces :
    yoneda.relativelyRepresentable ≤ representableByAlgebraicSpaces S := fun _ _ _ ha _ ξ ↦
  have ⟨V, _, _, h⟩ := ha ξ
  (isAlgebraicSpace S).prop_of_iso h.isoPullback (isAlgebraicSpace_yoneda S V)

/-- A morphism from an algebraic space to an fppf sheaf with diagonal representable by schemes is
representable by algebraic spaces: its base changes to schemes are fibre products of algebraic
spaces (Stacks 04T9). When the target is an algebraic space this is Stacks 03BN. -/
theorem representableByAlgebraicSpaces_of_isAlgebraicSpace {F G : (Over S)ᵒᵖ ⥤ Type u}
    (hF : isAlgebraicSpace S F) (hG : Presieve.IsSheaf (Scheme.fppfTopology.over S) G)
    (hΔ : yoneda.relativelyRepresentable (diag G)) (a : F ⟶ G) :
    representableByAlgebraicSpaces S a := fun _ ξ ↦
  isAlgebraicSpace_pullback hF (isAlgebraicSpace_yoneda S _) hG hΔ a ξ

/-- Every morphism of algebraic spaces over `S` is representable by algebraic spaces
(Stacks 03BN). -/
theorem AlgebraicSpace.representableByAlgebraicSpaces {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    AlgebraicGeometry.representableByAlgebraicSpaces S f.hom :=
  representableByAlgebraicSpaces_of_isAlgebraicSpace X.property Y.property.1 Y.property.2.1 f.hom

variable (S) in
/-- A morphism `a : F ⟶ G` of presheaves on `Over S` is **representable by algebraic spaces with
`P`** when it is representable by algebraic spaces and, for every map `ξ : yoneda.obj U ⟶ G` from
a scheme over `S`, some étale surjective atlas `v : yoneda.obj V ⟶ yoneda.obj U ×_G F` by a scheme
over `S` makes the composite scheme morphism `V ⟶ U` have `P`.

This is Stacks 03XZ for the property of morphisms of algebraic spaces that `P` induces through
étale atlases (Stacks 04RD). Without hypotheses on `P` the atlas matters. For instance, take
`P = @IsOpenImmersion` and the identity of `yoneda.obj X` for a scheme `X = Spec k` over `S`, with
`k` a field. Every base change is a scheme `U`, and the atlas `𝟙 U` makes the identity have `P`.
But the fold map `Spec k ⨿ Spec k ⟶ Spec k` is an étale surjective atlas of the base change along
`𝟙 X`, and it is not an open immersion. Under `MorphismProperty.RespectsLeft` and
`MorphismProperty.HasOfPrecompProperty` with respect to `@Etale ⊓ @Surjective`, one atlas suffices
exactly when every atlas does: `AlgebraicGeometry.representableByAlgebraicSpacesWith_iff_forall`.
`@IsOpenImmersion` fails `RespectsLeft`. -/
def representableByAlgebraicSpacesWith (P : MorphismProperty Scheme.{u}) :
    MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  fun _ G a ↦ representableByAlgebraicSpaces S a ∧ ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G),
    ∃ (V : Over S) (v : yoneda.obj V ⟶ pullback a ξ),
      (@Etale ⊓ @Surjective : MorphismProperty Scheme).over.presheaf v ∧
        P (Yoneda.fullyFaithful.preimage (v ≫ pullback.snd a ξ)).left

/-- An isomorphism of presheaves on `Over S` is an étale surjective atlas. -/
private lemma etale_inf_surjective_presheaf_of_isIso {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsIso f] : (@Etale ⊓ @Surjective : MorphismProperty Scheme.{u}).over.presheaf f := by
  let P : MorphismProperty Scheme.{u} := @Etale ⊓ @Surjective
  have : P.IsMultiplicative := IsMultiplicative.inf (P := @Etale) (Q := @Surjective)
  have : RespectsIso (@Etale : MorphismProperty Scheme.{u}) := IsStableUnderBaseChange.respectsIso
  have : P.RespectsIso := RespectsIso.inf _ _
  have : (P.over (X := S)).IsMultiplicative :=
    inferInstanceAs (P.inverseImage (Over.forget S)).IsMultiplicative
  have : (P.over (X := S)).RespectsIso :=
    inferInstanceAs (P.inverseImage (Over.forget S)).RespectsIso
  exact MorphismProperty.of_isIso _ f

/-- **Atlas independence.** For `P` stable under precomposition with étale surjections and
descending along them, a morphism representable by algebraic spaces has `P` on some étale
surjective atlas of each base change to a scheme exactly when it has `P` on every such atlas. Two
atlases are compared through their fibre product (compare Stacks 03MJ). -/
theorem representableByAlgebraicSpacesWith_iff_forall (P : MorphismProperty Scheme.{u})
    [P.RespectsLeft (@Etale ⊓ @Surjective)] [P.HasOfPrecompProperty (@Etale ⊓ @Surjective)]
    {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    representableByAlgebraicSpacesWith S P a ↔ representableByAlgebraicSpaces S a ∧
      ∀ ⦃U V : Over S⦄ (ξ : yoneda.obj U ⟶ G) (v : yoneda.obj V ⟶ pullback a ξ),
        (@Etale ⊓ @Surjective : MorphismProperty Scheme).over.presheaf v →
          P (Yoneda.fullyFaithful.preimage (v ≫ pullback.snd a ξ)).left := by
  refine ⟨fun ⟨ha, hex⟩ ↦ ⟨ha, fun U V ξ v hv ↦ ?_⟩, fun ⟨ha, hall⟩ ↦ ⟨ha, fun U ξ ↦ ?_⟩⟩
  · obtain ⟨V₀, v₀, hv₀, hP⟩ := hex ξ
    obtain ⟨W, s, t, h⟩ := hv.rep v₀
    have hs : (@Etale ⊓ @Surjective) s.left := hv.property v₀ t s h
    have ht : (@Etale ⊓ @Surjective) (Yoneda.fullyFaithful.preimage t).left :=
      hv₀.property v (yoneda.map s) _ (by rw [Functor.FullyFaithful.map_preimage]; exact h.flip)
    have key : s ≫ Yoneda.fullyFaithful.preimage (v₀ ≫ pullback.snd a ξ) =
        Yoneda.fullyFaithful.preimage t ≫ Yoneda.fullyFaithful.preimage (v ≫ pullback.snd a ξ) :=
      yoneda.map_injective (by simp [reassoc_of% h.w])
    have hsP := RespectsLeft.precomp (Q := @Etale ⊓ @Surjective) _ hs _ hP
    rw [← Over.comp_left, key, Over.comp_left] at hsP
    exact P.of_precomp _ _ ht hsP
  · obtain ⟨V, v, hv⟩ := (ha ξ).2.2
    exact ⟨V, v, hv, hall ξ v hv⟩

variable (S) in
/-- Morphisms representable by algebraic spaces with `P` are stable under base change
(Stacks 046F). No hypothesis on `P` is needed: an atlas of the base change of `a` along `ξ ≫ f` is
one of the base change of `a'` along `ξ`, with the same map to `U`. -/
instance (P : MorphismProperty Scheme.{u}) :
    (representableByAlgebraicSpacesWith S P).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ f g _ g'} sq hg := by
    refine ⟨IsStableUnderBaseChange.of_isPullback (P := representableByAlgebraicSpaces S) sq hg.1,
      fun U ξ ↦ ?_⟩
    have h := (IsPullback.of_hasPullback g' ξ).paste_horiz sq
    obtain ⟨V, v, hv, hP⟩ := hg.2 (ξ ≫ f)
    refine ⟨V, v ≫ h.isoPullback.inv, RespectsIso.postcomp _ _ _ hv, ?_⟩
    rwa [Category.assoc, h.isoPullback_inv_snd]

variable (S) in
/-- A morphism of presheaves whose base changes to schemes over `S` have `P` is representable by
algebraic spaces with `P`: each base change is a scheme and serves as its own atlas. -/
theorem presheaf_le_representableByAlgebraicSpacesWith (P : MorphismProperty Scheme.{u}) :
    (P.over (X := S)).presheaf ≤ representableByAlgebraicSpacesWith S P := by
  intro _ _ a ha
  refine ⟨relativelyRepresentable_le_representableByAlgebraicSpaces S a ha.rep, fun U ξ ↦ ?_⟩
  have h := ha.rep.isPullback ξ
  refine ⟨_, h.isoPullback.hom, etale_inf_surjective_presheaf_of_isIso _, ?_⟩
  rw [h.isoPullback_hom_snd, Functor.FullyFaithful.preimage_map]
  exact ha.property_snd ξ

end AlgebraicGeometry
