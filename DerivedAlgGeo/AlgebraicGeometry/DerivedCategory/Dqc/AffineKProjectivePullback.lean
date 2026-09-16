/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KProjective
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

/-- Extension of scalars along an arbitrary morphism of commutative rings
carries a quasi-isomorphism between K-projective complexes to a
quasi-isomorphism.

The ring map carries no flatness hypothesis: a quasi-isomorphism between
K-projective complexes is a homotopy equivalence, and extension of scalars is
additive. -/
theorem quasiIso_extendScalars_map_of_isKProjective
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {K L : _root_.CochainComplex (ModuleCat R) ℤ}
    [_root_.CochainComplex.IsKProjective K]
    [_root_.CochainComplex.IsKProjective L]
    {g : K ⟶ L}
    (hg : HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ) g) :
    HomologicalComplex.quasiIso (ModuleCat A) (ComplexShape.up ℤ)
      (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) :=
  _root_.CochainComplex.IsKProjective.quasiIso_map
    (ModuleCat.extendScalars f.hom) hg

/-- The inhabited form of `quasiIso_extendScalars_map_of_isKProjective`.

Bounded-above complexes of projective modules are K-projective and exist in
abundance over any ring, so this is the statement an affine consumer of
arbitrary derived pullback can actually apply. -/
theorem quasiIso_extendScalars_map_of_projective
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    {K L : _root_.CochainComplex (ModuleCat R) ℤ} (dK dL : ℤ)
    [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    [∀ n : ℤ, Projective (K.X n)] [∀ n : ℤ, Projective (L.X n)]
    {g : K ⟶ L}
    (hg : HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ) g) :
    HomologicalComplex.quasiIso (ModuleCat A) (ComplexShape.up ℤ)
      (((ModuleCat.extendScalars f.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) :=
  _root_.CochainComplex.IsKProjective.quasiIso_map_of_projective
    (ModuleCat.extendScalars f.hom) dK dL hg

end

end AlgebraicGeometry.DerivedCategory.Dqc
