/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec

/-!
# Nonflat affine pullback on an ambient K-flat model

For any ring map `R ⟶ A`, the canonical arbitrary left-derived pullback of a
sheafified module complex is represented by termwise scalar extension when the
sheafified input is K-flat for the ambient scheme-module total tensor. The
comparison is objectwise and does not supply that K-flat hypothesis for every
module complex or every object of `Dqc`.

## Main definitions

This file introduces no new carrier, class, or instance.

## Main results

* The right-tensor comparison identifies derived pullback with termwise
  scalar extension under the precise inversion premise.
* Its K-flat specialization uses a supplied ambient K-flat model.

## Implementation notes

The generic K-flat objectwise comparison identifies derived pullback with
ordinary pullback. The existing affine tilde/pullback natural isomorphism then
identifies that complex with sheafified termwise scalar extension. No
module-side derived tensor identification is used here.

## References

The comparison uses the repository's generic right-tensor comparison and
`AlgebraicGeometry.Scheme.Modules.pullbackSpecMapTildeMapHomologicalComplexIso`.

## Tags

affine scheme, derived pullback, K-flat, scalar extension
-/

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

/-- For any ring map, including a nonflat one, derived pullback of a sheafified
module complex agrees objectwise with sheafified termwise scalar extension if
right tensor with the sheafified input inverts quasi-isomorphisms. -/
def affineDerivedPullbackObjIsoOfTensorRightInverts
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (P : CochainComplex (ModuleCat R) ℤ)
    (hP : (HomologicalComplex.quasiIso (Spec R).Modules (ComplexShape.up ℤ)).IsInvertedBy
      ((Scheme.Modules.totalTensor (Spec R)).flip.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⋙
          DerivedCategory.Q)) :
    (arbitraryLeftDerivedPullback
      (toIdentityBaseChange (Over.mk (Spec.map f)))).functor.obj
      ((SchemeDerivedCategory.Q (Spec R)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≅
      (SchemeDerivedCategory.Q (Spec A)).obj
        (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) := by
  let e := Scheme.Modules.pullbackSpecMapTildeMapHomologicalComplexIso f
  exact (derivedPullbackObjIsoOfTensorRightInverts
      (toIdentityBaseChange (Over.mk (Spec.map f))) _ hP) ≪≫
    (SchemeDerivedCategory.Q (Spec A)).mapIso (e.app P)

/-- Ambient K-flatness supplies the right-tensor inversion premise for the
nonflat affine objectwise comparison. This does not infer ambient K-flatness
from a property of the module complex. -/
def affineDerivedPullbackObjIsoOfKFlat
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    (P : CochainComplex (ModuleCat R) ℤ)
    (hP : CochainComplex.IsKFlat (Scheme.Modules.totalTensor (Spec R))
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :
    (arbitraryLeftDerivedPullback
      (toIdentityBaseChange (Over.mk (Spec.map f)))).functor.obj
      ((SchemeDerivedCategory.Q (Spec R)).obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≅
      (SchemeDerivedCategory.Q (Spec A)).obj
        (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) :=
  affineDerivedPullbackObjIsoOfTensorRightInverts f P hP.2

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
