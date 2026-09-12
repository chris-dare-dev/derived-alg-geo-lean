/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineRealization
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Affine
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Transport

/-!
# Pushforward on affine quasi-coherent derived categories

For a ring map `R → S`, module-sheaf pushforward along
`Spec S → Spec R` preserves quasi-coherence. Restricted to the genuine
abelian categories of quasi-coherent sheaves, it is exact: left exactness
comes from ordinary pushforward, while right exactness follows from affine
pushforward preserving epimorphisms between quasi-coherent sheaves. It
therefore induces an exact functor on derived categories.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pseudofunctor

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

local instance affineQuasicoherentSheavesInclusion_full
    (R : CommRingCat.{u}) : (affineQuasicoherentSheavesInclusion R).Full :=
  (SheafOfModules.isQuasicoherent
    (Spec R).ringCatSheaf).fullyFaithfulι.full

local instance affineQuasicoherentSheavesInclusion_faithful
    (R : CommRingCat.{u}) : (affineQuasicoherentSheavesInclusion R).Faithful :=
  (SheafOfModules.isQuasicoherent
    (Spec R).ringCatSheaf).fullyFaithfulι.faithful

/-- Module-sheaf pushforward along a morphism of affine spectra, restricted
to genuine quasi-coherent sheaves. -/
def affineQuasicoherentSheavesPushforward
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    AffineQuasicoherentSheaves S ⥤ AffineQuasicoherentSheaves R :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward (Spec.map f))
    (fun M ↦ Scheme.Modules.isQuasicoherent_pushforward_SpecMap f M.obj)

/-- Forgetting quasi-coherence recovers ordinary module-sheaf pushforward. -/
def affineQuasicoherentSheavesPushforwardCompInclusion
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentSheavesPushforward f ⋙
        affineQuasicoherentSheavesInclusion R ≅
      affineQuasicoherentSheavesInclusion S ⋙
        Scheme.Modules.pushforward (Spec.map f) :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).liftCompιIso _ _

/-- Affine global sections identify quasi-coherent pushforward with
restriction of scalars. -/
def affineQuasicoherentSheavesPushforwardGammaIso
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentSheavesPushforward f ⋙
        (affineQuasicoherentSheavesEquiv R).inverse ≅
      (affineQuasicoherentSheavesEquiv S).inverse ⋙
        ModuleCat.restrictScalars f.hom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (affineQuasicoherentSheavesPushforwardCompInclusion f)
      (moduleSpecΓFunctor (R := R)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (affineQuasicoherentSheavesInclusion S)
      (gammaPushforwardNatIso f) ≪≫
    (Functor.associator _ _ _).symm

/-- Geometric affine quasi-coherent pushforward is restriction of scalars
transported through the affine equivalences. -/
def affineQuasicoherentSheavesPushforwardComparison
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentSheavesPushforward f ≅
      equivalenceTransportFunctor
        (affineQuasicoherentSheavesEquiv S)
        (affineQuasicoherentSheavesEquiv R)
        (ModuleCat.restrictScalars f.hom) := by
  let transported := equivalenceTransportFunctor
    (affineQuasicoherentSheavesEquiv S)
    (affineQuasicoherentSheavesEquiv R)
    (ModuleCat.restrictScalars f.hom)
  let cancel : transported ⋙ (affineQuasicoherentSheavesEquiv R).inverse ≅
      (affineQuasicoherentSheavesEquiv S).inverse ⋙
        ModuleCat.restrictScalars f.hom :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((affineQuasicoherentSheavesEquiv S).inverse ⋙
          ModuleCat.restrictScalars f.hom)
        (affineQuasicoherentSheavesEquiv R).unitIso.symm ≪≫
      Functor.rightUnitor _
  exact Functor.fullyFaithfulCancelRight
    (affineQuasicoherentSheavesEquiv R).inverse
    (affineQuasicoherentSheavesPushforwardGammaIso f ≪≫ cancel.symm)

/-- Affine quasi-coherent pushforward preserves finite limits. -/
instance affineQuasicoherentSheavesPushforward_preservesFiniteLimits
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteLimits (affineQuasicoherentSheavesPushforward f) :=
  haveI : PreservesFiniteLimits
      (affineQuasicoherentSheavesPushforward f ⋙
        affineQuasicoherentSheavesInclusion R) := by
    change PreservesFiniteLimits
      (affineQuasicoherentSheavesInclusion S ⋙
        Scheme.Modules.pushforward (Spec.map f))
    exact comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_reflects_of_preserves
    (affineQuasicoherentSheavesPushforward f)
    (affineQuasicoherentSheavesInclusion R)

/-- Affine quasi-coherent pushforward is additive. -/
instance affineQuasicoherentSheavesPushforward_additive
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (affineQuasicoherentSheavesPushforward f).Additive :=
  haveI : (affineQuasicoherentSheavesPushforward f ⋙
      affineQuasicoherentSheavesInclusion R).Additive := by
    change (affineQuasicoherentSheavesInclusion S ⋙
      Scheme.Modules.pushforward (Spec.map f)).Additive
    infer_instance
  Functor.additive_of_comp_faithful
    (affineQuasicoherentSheavesPushforward f)
    (affineQuasicoherentSheavesInclusion R)

/-- Affine quasi-coherent pushforward preserves epimorphisms. -/
instance affineQuasicoherentSheavesPushforward_preservesEpimorphisms
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (affineQuasicoherentSheavesPushforward f).PreservesEpimorphisms where
  preserves {M N} g _ := by
    haveI : (affineQuasicoherentSheavesInclusion S).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape
        (affineQuasicoherentSheavesInclusion S)
    haveI : Epi ((affineQuasicoherentSheavesInclusion S).map g) :=
      (affineQuasicoherentSheavesInclusion S).map_epi g
    haveI : ((affineQuasicoherentSheavesInclusion S).obj M).IsQuasicoherent :=
      M.property
    haveI : ((affineQuasicoherentSheavesInclusion S).obj N).IsQuasicoherent :=
      N.property
    apply (affineQuasicoherentSheavesInclusion R).epi_of_epi_map
    change Epi ((Scheme.Modules.pushforward (Spec.map f)).map
      ((affineQuasicoherentSheavesInclusion S).map g))
    exact Scheme.Modules.pushforward_map_epi_of_isAffineHom
      (Spec.map f) ((affineQuasicoherentSheavesInclusion S).map g)

/-- Affine quasi-coherent pushforward preserves finite colimits. -/
instance affineQuasicoherentSheavesPushforward_preservesFiniteColimits
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteColimits (affineQuasicoherentSheavesPushforward f) :=
  haveI : (affineQuasicoherentSheavesPushforward f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Exact pushforward on affine quasi-coherent derived categories. -/
def affineQuasicoherentDerivedPushforward
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    AffineQuasicoherentDerivedCategory S ⥤
      AffineQuasicoherentDerivedCategory R :=
  (affineQuasicoherentSheavesPushforward f).mapDerivedCategory

/-- Affine quasi-coherent derived pushforward preserves cohomologically
bounded objects. -/
theorem affineQuasicoherentDerivedPushforward_bounded
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (E : AffineQuasicoherentDerivedCategory S)
    (hE : (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves S)).bounded E) :
    (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves R)).bounded
        ((affineQuasicoherentDerivedPushforward f).obj E) :=
  mapDerivedCategory_bounded
    (affineQuasicoherentSheavesPushforward f) E hE

/-- Geometric affine derived pushforward restricted to cohomologically
bounded quasi-coherent complexes. -/
def affineQuasicoherentBoundedDerivedPushforward
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    AffineQuasicoherentBoundedDerivedCategory S ⥤
      AffineQuasicoherentBoundedDerivedCategory R :=
  (DerivedCategory.TStructure.t
    (C := AffineQuasicoherentSheaves R)).bounded.lift
      (DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentDerivedPushforward f)
      (fun E ↦ affineQuasicoherentDerivedPushforward_bounded
        f E.obj E.property)

/-- Forgetting boundedness recovers geometric affine derived pushforward. -/
def affineQuasicoherentBoundedDerivedPushforwardCompInclusion
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentBoundedDerivedPushforward f ⋙
        DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentDerivedPushforward f :=
  (DerivedCategory.TStructure.t
    (C := AffineQuasicoherentSheaves R)).bounded.liftCompιIso
      (DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentDerivedPushforward f)
      (fun E ↦ affineQuasicoherentDerivedPushforward_bounded
        f E.obj E.property)

/-- On derived categories, affine global sections identify geometric
pushforward with derived restriction of scalars. -/
def affineQuasicoherentDerivedPushforwardGammaIso
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentDerivedPushforward f ⋙
        affineGammaDerivedFunctor R ≅
      affineGammaDerivedFunctor S ⋙
        (ModuleCat.restrictScalars f.hom).mapDerivedCategory := by
  let H := (affineQuasicoherentSheavesEquiv S).inverse ⋙
    ModuleCat.restrictScalars f.hom
  letI : H.Additive := by dsimp [H]; infer_instance
  letI : PreservesFiniteLimits H := by
    dsimp [H]
    exact comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits H := by
    dsimp [H]
    exact comp_preservesFiniteColimits _ _
  exact Functor.mapDerivedCategoryCompIso
      (affineQuasicoherentSheavesPushforwardGammaIso f) ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl H)).symm

/-- Geometric affine derived pushforward is the transport of derived
restriction of scalars through the affine derived equivalences. -/
def affineQuasicoherentDerivedPushforwardComparison
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentDerivedPushforward f ≅
      equivalenceTransportFunctor
        (affineQuasicoherentDerivedEquivalence S)
        (affineQuasicoherentDerivedEquivalence R)
        ((ModuleCat.restrictScalars f.hom).mapDerivedCategory) := by
  let transported := equivalenceTransportFunctor
    (affineQuasicoherentDerivedEquivalence S)
    (affineQuasicoherentDerivedEquivalence R)
    ((ModuleCat.restrictScalars f.hom).mapDerivedCategory)
  let cancel : transported ⋙ affineGammaDerivedFunctor R ≅
      affineGammaDerivedFunctor S ⋙
        (ModuleCat.restrictScalars f.hom).mapDerivedCategory :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((affineQuasicoherentDerivedEquivalence S).inverse ⋙
          (ModuleCat.restrictScalars f.hom).mapDerivedCategory)
        (affineQuasicoherentDerivedEquivalence R).unitIso.symm ≪≫
      Functor.rightUnitor _
  letI : (affineGammaDerivedFunctor R).Full :=
    (affineQuasicoherentDerivedEquivalence R).fullyFaithfulInverse.full
  letI : (affineGammaDerivedFunctor R).Faithful :=
    (affineQuasicoherentDerivedEquivalence R).fullyFaithfulInverse.faithful
  exact Functor.fullyFaithfulCancelRight (affineGammaDerivedFunctor R)
    (affineQuasicoherentDerivedPushforwardGammaIso f ≪≫ cancel.symm)

end

end AlgebraicGeometry.DerivedCategory.Dqc
