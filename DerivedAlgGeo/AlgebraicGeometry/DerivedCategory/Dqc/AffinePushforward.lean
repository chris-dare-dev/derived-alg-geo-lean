/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineRealization
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Affine

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

end

end AlgebraicGeometry.DerivedCategory.Dqc
