/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.Algebra.Homology.Additive
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tensor extension and canonical module localization in `ModuleCat`

For the canonical ring `Localization S`, extension of scalars and Mathlib's
`localizedModuleFunctor S` are naturally isomorphic. The latter uses a
`Shrink` carrier, so the comparison is not definitional. Its component sends
the tensor generator `1 ⊗ m` to `localizedModuleMkLinearMap S m`.

The natural isomorphism also acts on cochain complexes. No arrow descent or
derived-category Hom localization is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped TensorProduct

noncomputable section

namespace ModuleCat

universe u

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The canonical scalar-extension/localized-module comparison at one module. -/
def extendScalarsLocalizationIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M ≅
      (ModuleCat.localizedModuleFunctor S).obj M := by
  have hScalar (r : R) (m : M.localizedModule S) :
      (algebraMap R (Localization S) r) • m = r • m :=
    IsScalarTower.algebraMap_smul (Localization S) r m
  let alg : Algebra R (Localization S) := inferInstance
  let hLoc : @IsLocalization R _ S (Localization S) _ alg := inferInstance
  have hAlgEq : (algebraMap R (Localization S)).toAlgebra = alg :=
    toAlgebra_algebraMap
  letI : Algebra R (Localization S) := (algebraMap R (Localization S)).toAlgebra
  letI : SMul R (Localization S) := Algebra.toSMul
  letI : Module R (Localization S) := Algebra.toModule
  haveI : IsLocalization S (Localization S) := by
    exact (congrArg
      (fun a : Algebra R (Localization S) =>
        @IsLocalization R _ S (Localization S) _ a) hAlgEq).mpr hLoc
  letI : IsScalarTower R (Localization S) (M.localizedModule S) :=
    .of_algebraMap_smul (fun r m => hScalar r m)
  let e : Localization S ⊗[R] M ≃ₗ[Localization S] M.localizedModule S :=
    (IsLocalizedModule.isBaseChange S (Localization S)
      (M.localizedModuleMkLinearMap S)).equiv
  exact
    { hom := ConcreteCategory.ofHom e.toLinearMap
      inv := ConcreteCategory.ofHom e.symm.toLinearMap
      hom_inv_id := by
        apply ModuleCat.hom_ext
        exact LinearMap.ext e.left_inv
      inv_hom_id := by
        apply ModuleCat.hom_ext
        exact LinearMap.ext e.right_inv }

/-- The component comparison agrees with the two localization generators. -/
theorem extendScalarsLocalizationIso_hom_tmul (M : ModuleCat.{u} R) (m : M) :
    (extendScalarsLocalizationIso S M).hom
        ((1 : Localization S) ⊗ₜ[R] m) =
      M.localizedModuleMkLinearMap S m := by
  unfold extendScalarsLocalizationIso
  change ((IsLocalizedModule.isBaseChange S (Localization S)
      (M.localizedModuleMkLinearMap S)).equiv)
        ((1 : Localization S) ⊗ₜ[R] m) = M.localizedModuleMkLinearMap S m
  simp

/-- Canonical natural isomorphism between tensor extension and localized modules. -/
def extendScalarsLocalizationNatIso :
    ModuleCat.extendScalars (algebraMap R (Localization S)) ≅
      ModuleCat.localizedModuleFunctor.{u} S :=
  NatIso.ofComponents (extendScalarsLocalizationIso S) (by
    intro M N f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (extendScalarsLocalizationIso S N).hom
        ((ModuleCat.extendScalars (algebraMap R (Localization S))).map f
          ((1 : Localization S) ⊗ₜ[R] m)) =
      (ModuleCat.localizedModuleFunctor S).map f
        ((extendScalarsLocalizationIso S M).hom
          ((1 : Localization S) ⊗ₜ[R] m))
    erw [ModuleCat.ExtendScalars.map_tmul]
    erw [extendScalarsLocalizationIso_hom_tmul]
    rw [extendScalarsLocalizationIso_hom_tmul]
    change (N.localizedModuleMkLinearMap S) (f.hom m) =
      (IsLocalizedModule.mapExtendScalars S
        (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
        (Localization S) f.hom) (M.localizedModuleMkLinearMap S m)
    rw [IsLocalizedModule.mapExtendScalars_apply_apply,
      IsLocalizedModule.map_apply])

/-- The comparison on cochain complexes is induced degreewise by the
canonical natural isomorphism of module functors. -/
def extendScalarsLocalizationCochainNatIso :
    (ModuleCat.extendScalars (algebraMap R (Localization S))).mapHomologicalComplex
        (.up ℤ) ≅
      (ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex (extendScalarsLocalizationNatIso S) (.up ℤ)

end ModuleCat

end
