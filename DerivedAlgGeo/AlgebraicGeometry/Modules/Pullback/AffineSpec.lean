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
adjunctions and the affine global-sections comparison. Its mate equation below
identifies the actual pullback unit on top sections with the tensor generator.
-/

universe u

open CategoryTheory
open scoped ChangeOfRings
open scoped TensorProduct

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

/-- The affine tilde/pullback comparison is the mate of the *actual* scheme-module pullback
unit. After identifying the two global-sections functors, this equation says that applying
`pullbackSpecMapTildeIso` to the section obtained from that unit agrees with the tensor
extension unit followed by the target tilde/Γ unit. No localization or derived claim enters. -/
theorem pullbackSpecMapTildeIso_unit (M : ModuleCat.{u} R) :
    (AlgebraicGeometry.tilde.isoTop M).hom ≫
      (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).map
        ((pullbackPushforwardAdjunction (Spec.map f)).unit.app (AlgebraicGeometry.tilde M)) ≫
      (AlgebraicGeometry.gammaPushforwardNatIso f).hom.app
        ((pullback (Spec.map f)).obj (AlgebraicGeometry.tilde M)) ≫
      (ModuleCat.restrictScalars f.hom).map
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := S)).map
          ((pullbackSpecMapTildeIso f).hom.app M)) =
    (ModuleCat.extendRestrictScalarsAdj f.hom).unit.app M ≫
      (ModuleCat.restrictScalars f.hom).map
        ((AlgebraicGeometry.tilde.adjunction (R := S)).unit.app
          ((ModuleCat.extendScalars f.hom).obj M)) := by
  let adjL := ((AlgebraicGeometry.tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map f))).ofNatIsoRight
      (AlgebraicGeometry.gammaPushforwardNatIso f)
  let adjR := (ModuleCat.extendRestrictScalarsAdj f.hom).comp
    (AlgebraicGeometry.tilde.adjunction (R := S))
  have h := adjL.unit_leftAdjointUniq_hom_app adjR M
  have he : pullbackSpecMapTildeIso f = adjL.leftAdjointUniq adjR := rfl
  rw [← he] at h
  simp only [adjL, adjR, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.comp_map, Adjunction.comp_unit_app] at h
  simp only [Category.assoc] at h ⊢
  exact h

/-- On a section `m`, the actual affine pullback unit becomes `1 ⊗ m` under the
tilde/Γ and affine pullback comparisons. The right-hand side is the canonical section of the
tilde of the scalar-extended module, not a chosen non-natural Γ isomorphism. -/
theorem pullbackSpecMapTildeIso_unit_apply (M : ModuleCat.{u} R) (m : M) :
    ((AlgebraicGeometry.tilde.isoTop M).hom ≫
      (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).map
        ((pullbackPushforwardAdjunction (Spec.map f)).unit.app (AlgebraicGeometry.tilde M)) ≫
      (AlgebraicGeometry.gammaPushforwardNatIso f).hom.app
        ((pullback (Spec.map f)).obj (AlgebraicGeometry.tilde M)) ≫
      (ModuleCat.restrictScalars f.hom).map
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := S)).map
          ((pullbackSpecMapTildeIso f).hom.app M))).hom m =
    (AlgebraicGeometry.tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom
      ((1 : S) ⊗ₜ[R] m) := by
  have h := congrArg (fun g : M ⟶
      (ModuleCat.restrictScalars f.hom).obj
        ((AlgebraicGeometry.moduleSpecΓFunctor (R := S)).obj
          (AlgebraicGeometry.tilde ((ModuleCat.extendScalars f.hom).obj M))) => g.hom m)
      (pullbackSpecMapTildeIso_unit f M)
  calc
    _ = ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app M ≫
          (ModuleCat.restrictScalars f.hom).map
            ((AlgebraicGeometry.tilde.adjunction (R := S)).unit.app
              ((ModuleCat.extendScalars f.hom).obj M))).hom m := h
    _ = _ := by
      rw [ModuleCat.hom_comp]
      change (AlgebraicGeometry.tilde.isoTop ((ModuleCat.extendScalars f.hom).obj M)).hom
        ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app M m) = _
      rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
      rfl

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
