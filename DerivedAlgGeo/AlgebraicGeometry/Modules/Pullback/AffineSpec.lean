/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Affine
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Additive
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Module pullback on affine spectra

For a map of commutative rings, pulling back the tilde of a module along the
induced map of affine schemes agrees with extension of scalars followed by
tilde. The comparison is underived and is obtained from the two standard
adjunctions and the affine global-sections comparison.
-/

universe u

open CategoryTheory
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Extension of scalars between module categories is additive. -/
private instance extendScalars_additive :
    (ModuleCat.extendScalars f.hom).Additive where
  map_add {M N} g h := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    let φ : R →+* S := f.hom
    letI : Module R S := Module.compHom S φ
    change (1 : S) ⊗ₜ[R,φ] (g m + h m) =
      (1 : S) ⊗ₜ[R,φ] g m + (1 : S) ⊗ₜ[R,φ] h m
    rw [TensorProduct.tmul_add]

/-- On affine spectra, scheme-module pullback after tilde is extension of
scalars followed by target tilde. This is an isomorphism of ordinary
functors; it does not assert that either side computes a derived pullback. -/
noncomputable def pullbackSpecMapTildeIso :
    AlgebraicGeometry.tilde.functor R ⋙
        Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ AlgebraicGeometry.tilde.functor S := by
  let adjL :=
    (AlgebraicGeometry.tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
  let adjR :=
    (ModuleCat.extendRestrictScalarsAdj f.hom).comp
      (AlgebraicGeometry.tilde.adjunction (R := S))
  exact Adjunction.leftAdjointUniq
    (adjL.ofNatIsoRight (AlgebraicGeometry.gammaPushforwardNatIso f)) adjR

/-- The affine tilde/pullback comparison induces the corresponding
isomorphism on cochain complexes. -/
noncomputable def pullbackSpecMapTildeMapHomologicalComplexIso :
    (AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.pullback (Spec.map f)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars f.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (AlgebraicGeometry.tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ) := by
  letI : (ModuleCat.extendScalars f.hom).Additive := extendScalars_additive f
  letI : (AlgebraicGeometry.tilde.functor R).Additive := inferInstance
  letI : (AlgebraicGeometry.tilde.functor S).Additive := inferInstance
  letI : (Scheme.Modules.pullback (Spec.map f)).Additive := inferInstance
  letI : (AlgebraicGeometry.tilde.functor R ⋙
      Scheme.Modules.pullback (Spec.map f)).Additive := inferInstance
  letI : (ModuleCat.extendScalars f.hom ⋙
      AlgebraicGeometry.tilde.functor S).Additive := inferInstance
  exact Functor.mapHomologicalComplexCompIso
    (pullbackSpecMapTildeIso f) (ComplexShape.up ℤ)

end AlgebraicGeometry.Scheme.Modules
