/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.KProjective
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Affine

/-!
# Affine derived pullback from K-projective complexes

This file applies the generic K-projective derived-functor API to extension
of scalars along an arbitrary morphism of commutative rings.  No flatness
hypothesis is imposed.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars is additive. -/
instance affineExtendScalars_additive
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (ModuleCat.extendScalars f.hom).Additive where
  map_add {M N} g h := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let φ : R →+* A := f.hom
    letI : Module R A := Module.compHom A φ
    change (1 : A) ⊗ₜ[R,φ] (g m + h m) =
      (1 : A) ⊗ₜ[R,φ] g m + (1 : A) ⊗ₜ[R,φ] h m
    rw [TensorProduct.tmul_add]

/-- Arbitrary extension of scalars on affine K-projective representatives. -/
def affineKProjectivePullback {R A : CommRingCat.{u}} (f : R ⟶ A) :
    KProjectiveHomotopyCategory (ModuleCat R) ⥤
      DerivedCategory (ModuleCat A) :=
  kProjectiveDerivedFunctor (ModuleCat.extendScalars f.hom)

/-- Arbitrary affine derived pullback on the full K-projective derived locus. -/
def affineKProjectiveDerivedPullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    KProjectiveDerivedCategory (ModuleCat R) ⥤
      DerivedCategory (ModuleCat A) :=
  kProjectiveLocusDerivedFunctor (ModuleCat.extendScalars f.hom)

/-- The derived-locus construction agrees with extension of scalars on
actual K-projective representatives. -/
def affineKProjectiveDerivedPullbackComparison
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (kProjectiveQhEquivalence (ModuleCat R)).functor ⋙
        affineKProjectiveDerivedPullback f ≅
      affineKProjectivePullback f :=
  kProjectiveLocusDerivedComparison (ModuleCat.extendScalars f.hom)

/-- A bounded-above complex of projective `R`-modules computes arbitrary
affine derived pullback by degreewise extension of scalars. -/
def affineKProjectivePullbackObjIso {R A : CommRingCat.{u}} (f : R ⟶ A)
    (K : CochainComplex (ModuleCat R) ℤ) (d : ℤ) [K.IsStrictlyLE d]
    [∀ n : ℤ, Projective (K.X n)] :
    (affineKProjectivePullback f).obj
        (KProjectiveHomotopyCategory.ofBoundedAboveProjectives K d) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  kProjectiveDerivedFunctorObjIso (ModuleCat.extendScalars f.hom) K d

end

end AlgebraicGeometry.DerivedCategory.Dqc
