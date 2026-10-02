/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineRGammaPlus
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.UnitExt
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundleLinear

/-!
# Evaluation into bounded-below derived affine sections

The single-object H⁰ comparison sends the identity of the structure sheaf
to a class in derived affine sections. Applying derived sections and H⁰ to a
map out of the structure sheaf, then evaluating at that class, gives an
additive and target-natural map on arbitrary bounded-below derived objects.

The map is not asserted bijective here. In particular, this file does not
identify H⁰ of derived sections of an arbitrary Dqc object with ordinary
sections of its degree-zero cohomology sheaf.

## Main definitions

* `affineRGammaPlusUnitClass` is the image of the structure-sheaf identity.
* `affineRGammaPlusEval` and `affineRGammaPlusEvalAddHom` are the specific
  evaluation map, as a function and additive homomorphism.

## Main results

`affineRGammaPlusEval_naturality` gives target naturality.

## Implementation notes

The existing single-object H⁰ comparison constructs the distinguished
class. Generic additivity of bounded-below right-derived functors makes
evaluation additive. No injective model or inverse is chosen in this file.

## References

`affineRGammaPlusHomologyZeroSingleIso` and
`Scheme.Modules.unitHomTopLinearEquiv` in this repository; Mathlib
`RightDerivedFunctorPlus.lean` at pin
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

affine scheme, derived global sections, evaluation, bounded below
-/

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Cohomology

/-- The class of the identity of the structure sheaf, transported through
the existing H⁰ comparison on a degree-zero single object. -/
noncomputable def affineRGammaPlusUnitClass (R : CommRingCat.{u}) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).obj
      ((affineRGammaPlus R).obj
        ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
          (Scheme.Modules.unit (Spec R)))) :=
  (affineRGammaPlusHomologyZeroSingleIso R (Scheme.Modules.unit (Spec R))).inv.hom
    ((Scheme.Modules.unitHomTopLinearEquiv (Scheme.Modules.unit (Spec R)))
      (𝟙 (Scheme.Modules.unit (Spec R))))

/-- Apply bounded-below derived affine sections to a map out of the
structure sheaf and evaluate its H⁰ map at `affineRGammaPlusUnitClass`.
This is the specific map whose injective-model comparison remains to be
proved; no inverse is claimed. -/
noncomputable def affineRGammaPlusEval (R : CommRingCat.{u})
    (M : DerivedCategory.Plus (Spec R).Modules)
    (f : ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶ M) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).obj
      ((affineRGammaPlus R).obj M) :=
  (((affineRGammaPlus R) ⋙
      (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0)).map f).hom
        (affineRGammaPlusUnitClass R)

/-- Naturality in the bounded-below target follows from functoriality of
derived affine sections. -/
theorem affineRGammaPlusEval_naturality (R : CommRingCat.{u})
    {M N : DerivedCategory.Plus (Spec R).Modules}
    (f : ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶ M) (g : M ⟶ N) :
    affineRGammaPlusEval R N (f ≫ g) =
      (((affineRGammaPlus R) ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0)).map g).hom
          (affineRGammaPlusEval R M f) := by
  simp only [affineRGammaPlusEval, Functor.comp_map, Functor.map_comp]
  exact ModuleCat.comp_apply _ _ _

/-- The canonical evaluation map is additive. Additivity of bounded-below
derived affine sections follows from the generic injective-model theorem;
it is not supplied as an extra hypothesis. -/
noncomputable def affineRGammaPlusEvalAddHom (R : CommRingCat.{u})
    (M : DerivedCategory.Plus (Spec R).Modules) :
    (((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶ M) →+
    (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).obj
      ((affineRGammaPlus R).obj M) := by
  haveI : (AlgebraicGeometry.affineΓ R).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (affineRGammaPlus R).Additive :=
    (AlgebraicGeometry.affineΓ R).rightDerivedFunctorPlus_additive
  haveI : (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).Additive := inferInstance
  haveI : ((affineRGammaPlus R) ⋙
      (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0)).Additive := inferInstance
  exact {
    toFun := affineRGammaPlusEval R M
    map_zero' := by
      change (((affineRGammaPlus R ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map
          (0 : _ ⟶ M)).hom (affineRGammaPlusUnitClass R)) = 0
      rw [Functor.map_zero]
      rfl
    map_add' := by
      intro f g
      change (((affineRGammaPlus R ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map
          (f + g)).hom (affineRGammaPlusUnitClass R)) =
        (((affineRGammaPlus R ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map f).hom
          (affineRGammaPlusUnitClass R)) +
        (((affineRGammaPlus R ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map g).hom
          (affineRGammaPlusUnitClass R))
      rw [Functor.map_add]
      rfl
  }

end AlgebraicGeometry.Cohomology
