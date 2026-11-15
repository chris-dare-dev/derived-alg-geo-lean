/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Cancellation for morphisms locally of finite presentation

If `f ≫ g` is locally of finite presentation and `g` is locally of finite type, then `f` is
locally of finite presentation (Stacks 02FV, first part). This is the finite-presentation companion
of Mathlib's `locallyOfFiniteType_of_comp`.

## Main definitions

* The instance `MorphismProperty.HasOfPostcompProperty @LocallyOfFinitePresentation
  @LocallyOfFiniteType`.

## Main results

* `LocallyOfFinitePresentation.of_comp`.

## Implementation notes

The proof follows Mathlib's `HasRingHomProperty.of_comp`: both properties are local on the source
and on the target, which reduces the claim to affine `X`, `Y` and `Z`. There it is
`RingHom.FinitePresentation.of_comp_finiteType` (Stacks 0561). Mathlib's `of_comp` does not apply
directly because the ring-level cancellation needs the finite-type hypothesis on `g`.

## References

* [Stacks, Lemma 29.22.11 (Tag 02FV)](https://stacks.math.columbia.edu/tag/02FV).

## Tags

locally of finite presentation, locally of finite type, cancellation
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f ≫ g` is locally of finite presentation and `g` is locally of finite type, then `f` is
locally of finite presentation. -/
@[stacks 02FV]
theorem LocallyOfFinitePresentation.of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  suffices ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), LocallyOfFinitePresentation (f ≫ g) →
      LocallyOfFiniteType g → LocallyOfFinitePresentation f from this f g ‹_› ‹_›
  intro X Y Z f g hfg hg
  wlog hZ : IsAffine Z generalizing X Y Z with H
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have hfg' := IsZariskiLocalAtTarget.restrict hfg U.1
    rw [morphismRestrict_comp] at hfg'
    exact H _ _ hfg' (IsZariskiLocalAtTarget.restrict hg U.1) U.2
  wlog hY : IsAffine Y generalizing X Y with H
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have hfg' := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      (f ⁻¹ᵁ U.1).ι (f ≫ g) hfg
    rw [← morphismRestrict_ι_assoc] at hfg'
    exact H _ _ hfg'
      (HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFiniteType U.1.ι g hg) U.2
  wlog hX : IsAffine X generalizing X with H
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have hfg' := HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      U.1.ι (f ≫ g) hfg
    rw [← Category.assoc] at hfg'
    exact H _ hfg' U.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at hfg ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hfg
  exact RingHom.FinitePresentation.of_comp_finiteType _ hfg hg

instance : MorphismProperty.HasOfPostcompProperty
    @LocallyOfFinitePresentation @LocallyOfFiniteType where
  of_postcomp f g _ _ := .of_comp f g

end AlgebraicGeometry
