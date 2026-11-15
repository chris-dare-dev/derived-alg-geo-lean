/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Localization.LocallySmall
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.Resolution

/-!
# Small Hom types in the derived category

Let `C` be an abelian category with `Category.{v} C`. If every cochain complex over `C`
has a quasi-isomorphism to a K-injective complex, then the Hom types of `D(C)` are
`v`-small: a morphism `K ⟶ I` in `D(C)` into a K-injective `I` is a homotopy class of
morphisms of complexes. This holds for every Grothendieck abelian category, so such a
category has a derived category whose morphisms live in the universe `v` of its own
morphisms.

## Main definitions

* `HasDerivedCategory.ofIsGrothendieckAbelian`: a derived category of a Grothendieck
  abelian category `C` with Hom types in `Type v`.

## Main results

* `DerivedCategory.locallySmall_of_exists_isKInjective_quasiIso`: `D(C)` is locally
  `v`-small when K-injective resolutions exist.
* `DerivedCategory.locallySmall_of_isGrothendieckAbelian`: the instance for a
  Grothendieck abelian category.

## Implementation notes

`HasDerivedCategory.standard` has Hom types in `Type (max u v)` for `C : Type u`. For
module sheaves on `X : Scheme.{u}` that is `Type (u + 1)`, one universe above the
morphisms of `X.Modules`. `HasDerivedCategory.ofIsGrothendieckAbelian` shrinks the Hom
types of the standard localization with Mathlib's
`MorphismProperty.hasLocalizationOfLocallySmall`. Like `HasDerivedCategory.standard`,
it is a definition for consumers to make a local instance, not a global instance.

## References

* [The Stacks project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988)

## Tags

derived category, locally small, K-injective resolution, Grothendieck abelian category
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w' w v u

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DerivedCategory

variable [HasDerivedCategory.{w'} C]

/-- If every cochain complex over `C` has a quasi-isomorphism to a K-injective complex,
then the Hom types of `D(C)` are `v`-small. -/
theorem locallySmall_of_exists_isKInjective_quasiIso
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (i : K ⟶ I), I.IsKInjective ∧ QuasiIso i) :
    LocallySmall.{v} (DerivedCategory C) where
  hom_small X Y := by
    obtain ⟨I, i, hI, hi⟩ := h (Q.objPreimage Y)
    let eX : X ≅ Qh.obj ((HomotopyCategory.quotient C _).obj (Q.objPreimage X)) :=
      (Q.objObjPreimageIso X).symm ≪≫ (quotientCompQhIso C).symm.app _
    let eY : Y ≅ Qh.obj ((HomotopyCategory.quotient C _).obj I) :=
      (Q.objObjPreimageIso Y).symm ≪≫ asIso (Q.map i) ≪≫ (quotientCompQhIso C).symm.app I
    have : Small.{v} (Qh.obj ((HomotopyCategory.quotient C _).obj (Q.objPreimage X)) ⟶
        Qh.obj ((HomotopyCategory.quotient C _).obj I)) :=
      small_of_surjective (CochainComplex.IsKInjective.Qh_map_bijective _ I).surjective
    exact small_map (eX.homCongr eY)

/-- The Hom types of the derived category of a Grothendieck abelian category `C` are
`v`-small. -/
instance locallySmall_of_isGrothendieckAbelian [IsGrothendieckAbelian.{w} C] :
    LocallySmall.{v} (DerivedCategory C) :=
  locallySmall_of_exists_isKInjective_quasiIso fun K =>
    ⟨_, (CochainComplex.kInjectiveResolutionι C).app K, inferInstance, inferInstance⟩

end DerivedCategory

variable (C) in
/-- A derived category of a Grothendieck abelian category `C` whose Hom types are in the
universe `v` of the morphisms of `C`, obtained by shrinking those of
`HasDerivedCategory.standard`. -/
@[instance_reducible]
noncomputable def HasDerivedCategory.ofIsGrothendieckAbelian [IsGrothendieckAbelian.{w} C] :
    HasDerivedCategory.{v} C :=
  letI := HasDerivedCategory.standard C
  MorphismProperty.hasLocalizationOfLocallySmall.{v} _ DerivedCategory.Q
