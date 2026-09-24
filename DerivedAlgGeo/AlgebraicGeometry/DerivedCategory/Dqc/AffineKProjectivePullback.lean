/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KProjective
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Affine
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.AffineSpec
import Mathlib.AlgebraicGeometry.Modules.Tilde

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

/-- On the affine K-projective derived locus, actual pullback of the
sheafified representatives agrees after localization with scalar extension
followed by the derived functor of the target affine tilde functor. The target
is the derived category of all scheme-module sheaves on `Spec A`, not only the
quasi-coherent subcategory. -/
noncomputable def affineKProjectiveSchemeModulePullbackComparison
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    CategoryTheory.kProjectiveLocusDerivedFunctor
        (AlgebraicGeometry.tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f)) ≅
      affineKProjectiveDerivedPullback f ⋙
        (AlgebraicGeometry.tilde.functor A).mapDerivedCategory := by
  let F := AlgebraicGeometry.tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f)
  let G := ModuleCat.extendScalars f.hom
  let T := AlgebraicGeometry.tilde.functor A
  let c := ComplexShape.up ℤ
  let QhS := DerivedCategory.Qh (C := ModuleCat A)
  let QhTarget := DerivedCategory.Qh (C := (Spec A).Modules)
  let E := CategoryTheory.kProjectiveQhEquivalence (ModuleCat R)
  let I := ObjectProperty.ι (CategoryTheory.kProjectiveHomotopy (ModuleCat R))
  letI : (AlgebraicGeometry.tilde.functor R).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor
  letI : (AlgebraicGeometry.tilde.functor A).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor
  letI : G.Additive := affineExtendScalars_additive f
  letI : F.Additive := inferInstance
  letI : (G ⋙ T).Additive := inferInstance
  letI : T.Additive := inferInstance
  letI : PreservesFiniteLimits T := AlgebraicGeometry.tilde_preservesFiniteLimits
  letI : T.IsLeftAdjoint := (AlgebraicGeometry.tilde.adjunction (R := A)).isLeftAdjoint
  letI : PreservesFiniteColimits T := inferInstance
  let e : F ≅ G ⋙ T := Scheme.Modules.pullbackSpecMapTildeIso f
  let eF : (AlgebraicGeometry.tilde.functor R).mapHomotopyCategory c ⋙
      (Scheme.Modules.pullback (Spec.map f)).mapHomotopyCategory c ≅
      F.mapHomotopyCategory c :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl F) c
  let eTop : (AlgebraicGeometry.tilde.functor R).mapHomotopyCategory c ⋙
      (Scheme.Modules.pullback (Spec.map f)).mapHomotopyCategory c ≅
      (G ⋙ T).mapHomotopyCategory c :=
    Functor.mapHomotopyCategoryCompIso e c
  let eG : G.mapHomotopyCategory c ⋙ T.mapHomotopyCategory c ≅
      (G ⋙ T).mapHomotopyCategory c :=
    Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ T)) c
  let eHC : F.mapHomotopyCategory c ≅
      (G.mapHomotopyCategory c ⋙ T.mapHomotopyCategory c) :=
    eF.symm ≪≫ eTop ≪≫ eG.symm
  let factorT : QhS ⋙ T.mapDerivedCategory ≅ T.mapHomotopyCategory c ⋙ QhTarget :=
    T.mapDerivedCategoryFactorsh
  let eT : (G.mapHomotopyCategory c ⋙ QhS) ⋙ T.mapDerivedCategory ≅
      (G.mapHomotopyCategory c ⋙ T.mapHomotopyCategory c) ⋙ QhTarget := by
    exact Functor.associator (G.mapHomotopyCategory c) QhS T.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (G.mapHomotopyCategory c) factorT ≪≫
      (Functor.associator (G.mapHomotopyCategory c) (T.mapHomotopyCategory c)
        QhTarget).symm
  let eMiddle : F.mapHomotopyCategory c ⋙ QhTarget ≅
      (G.mapHomotopyCategory c ⋙ QhS) ⋙ T.mapDerivedCategory := by
    exact Functor.isoWhiskerRight eHC QhTarget ≪≫ eT.symm
  let eFull : CategoryTheory.kProjectiveDerivedFunctor F ≅
      CategoryTheory.kProjectiveDerivedFunctor G ⋙ T.mapDerivedCategory := by
    dsimp [CategoryTheory.kProjectiveDerivedFunctor]
    exact Functor.isoWhiskerLeft I eMiddle ≪≫
      (Functor.associator I (G.mapHomotopyCategory c ⋙ QhS) T.mapDerivedCategory).symm
  dsimp [CategoryTheory.kProjectiveLocusDerivedFunctor,
    affineKProjectiveDerivedPullback,
    CategoryTheory.kProjectiveDerivedFunctor]
  exact Functor.isoWhiskerLeft E.inverse eFull ≪≫
    (Functor.associator E.inverse (CategoryTheory.kProjectiveDerivedFunctor G)
      T.mapDerivedCategory).symm

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
