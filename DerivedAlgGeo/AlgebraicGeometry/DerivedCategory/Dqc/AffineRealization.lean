/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.Preadditive.LeftExact
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Quasicoherent.Kernels
import DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineDerivedEquivalence

/-!
# Realizing the affine quasi-coherent derived category inside `Dqc`

On an affine spectrum, ambient kernels and cokernels of quasi-coherent module
sheaves are again quasi-coherent.  Hence the inclusion of quasi-coherent
sheaves into all module sheaves is exact.  Passing to derived categories and
using exactness to identify cohomology gives a concrete functor from the
derived category of affine quasi-coherent sheaves into the honest
quasi-coherent-cohomology locus `Dqc(Spec R)`.

This does not claim that the resulting functor is essentially surjective on
the unbounded `Dqc` locus.  That general affine realization theorem requires
additional unbounded derived-category input.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

private abbrev affineQuasicoherentProperty (R : CommRingCat.{u}) :=
  SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf

/-- On an affine spectrum, an ambient kernel of a morphism between
quasi-coherent module sheaves is quasi-coherent.

The proof moved to `CoherentSheaf/Quasicoherent/Kernels.lean` when #720 needed it
for an arbitrary scheme; this name survives as the moduli lane's entry point. -/
theorem affineQuasicoherent_kernel {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (g : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (kernel g).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_kernel_affine g hM hN

/-- Quasi-coherent module sheaves on an affine spectrum are closed under
ambient kernels. -/
instance affineQuasicoherent_isClosedUnderKernels (R : CommRingCat.{u}) :
    (affineQuasicoherentProperty R).IsClosedUnderKernels :=
  AlgebraicGeometry.quasicoherent_isClosedUnderKernels (Spec R)

/-- On an affine spectrum, an ambient cokernel of a morphism between
quasi-coherent module sheaves is quasi-coherent. -/
theorem affineQuasicoherent_cokernel {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (g : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (cokernel g).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_cokernel_affine g hM hN

/-- Quasi-coherent module sheaves on an affine spectrum are closed under
ambient cokernels. -/
instance affineQuasicoherent_isClosedUnderCokernels (R : CommRingCat.{u}) :
    (affineQuasicoherentProperty R).IsClosedUnderCokernels :=
  AlgebraicGeometry.quasicoherent_isClosedUnderCokernels (Spec R)

/-- The inclusion of affine quasi-coherent sheaves into all module sheaves. -/
abbrev affineQuasicoherentSheavesInclusion (R : CommRingCat.{u}) :
    AffineQuasicoherentSheaves R ⥤ (Spec R).Modules :=
  ObjectProperty.ι (affineQuasicoherentProperty R)

instance affineQuasicoherentSheavesInclusion_additive
    (R : CommRingCat.{u}) :
    (affineQuasicoherentSheavesInclusion R).Additive where
  map_add := rfl

noncomputable instance affineQuasicoherentSheavesInclusion_preservesKernel
    (R : CommRingCat.{u}) {M N : AffineQuasicoherentSheaves R}
    (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0)
      (affineQuasicoherentSheavesInclusion R) :=
  (affineQuasicoherentProperty R).preservesKernels_ι g

noncomputable instance affineQuasicoherentSheavesInclusion_preservesCokernel
    (R : CommRingCat.{u}) {M N : AffineQuasicoherentSheaves R}
    (g : M ⟶ N) :
    PreservesColimit (parallelPair g 0)
      (affineQuasicoherentSheavesInclusion R) :=
  (affineQuasicoherentProperty R).preservesCokernels_ι g

/-- The affine quasi-coherent inclusion preserves all finite limits. -/
noncomputable instance affineQuasicoherentSheavesInclusion_preservesFiniteLimits
    (R : CommRingCat.{u}) :
    PreservesFiniteLimits (affineQuasicoherentSheavesInclusion R) :=
  Functor.preservesFiniteLimits_of_preservesKernels
    (affineQuasicoherentSheavesInclusion R)

/-- The affine quasi-coherent inclusion preserves all finite colimits. -/
noncomputable instance affineQuasicoherentSheavesInclusion_preservesFiniteColimits
    (R : CommRingCat.{u}) :
    PreservesFiniteColimits (affineQuasicoherentSheavesInclusion R) :=
  Functor.preservesFiniteColimits_of_preservesCokernels
    (affineQuasicoherentSheavesInclusion R)

/-- Exactness of tilde follows from its factorization through the affine
quasi-coherent equivalence and the exact inclusion. -/
noncomputable instance affineTilde_preservesFiniteLimits
    (R : CommRingCat.{u}) : PreservesFiniteLimits (tilde.functor R) := by
  letI : PreservesFiniteLimits
      (affineQuasicoherentSheavesEquiv R).functor := inferInstance
  letI : PreservesFiniteLimits
      (affineQuasicoherentSheavesInclusion R) := inferInstance
  change PreservesFiniteLimits
    ((affineQuasicoherentSheavesEquiv R).functor ⋙
      affineQuasicoherentSheavesInclusion R)
  exact comp_preservesFiniteLimits _ _

/-- The exact inclusion of affine quasi-coherent sheaves induces a functor
into the ambient derived category of all module sheaves. -/
noncomputable def affineQuasicoherentDerivedInclusion
    (R : CommRingCat.{u}) :
    AffineQuasicoherentDerivedCategory R ⥤ SchemeDerivedCategory (Spec R) :=
  (affineQuasicoherentSheavesInclusion R).mapDerivedCategory

/-- Every object in the image of the affine derived inclusion has
quasi-coherent cohomology. -/
theorem affineQuasicoherentDerivedInclusion_mem_dqc
    (R : CommRingCat.{u}) (E : AffineQuasicoherentDerivedCategory R) :
    schemeQuasicoherentCohomology (Spec R)
      ((affineQuasicoherentDerivedInclusion R).obj E) := by
  intro n
  let H :=
    (DerivedCategory.homologyFunctor (AffineQuasicoherentSheaves R) n).obj E
  exact (affineQuasicoherentProperty R).prop_of_iso
    (mapDerivedCategoryHomologyIso
      (affineQuasicoherentSheavesInclusion R)
      (by infer_instance) (by infer_instance) (by infer_instance) E n).symm
    H.property

/-- The genuine affine quasi-coherent derived category maps concretely into
the honest quasi-coherent-cohomology locus `Dqc(Spec R)`. -/
noncomputable def affineQuasicoherentDerivedToDqc
    (R : CommRingCat.{u}) :
    AffineQuasicoherentDerivedCategory R ⥤
      SchemeQuasicoherentDerivedCategory (Spec R) :=
  (schemeQuasicoherentCohomology (Spec R)).lift
    (affineQuasicoherentDerivedInclusion R)
    (affineQuasicoherentDerivedInclusion_mem_dqc R)

/-- Forgetting the quasi-coherent-cohomology proof recovers the exact affine
derived inclusion. -/
noncomputable def affineQuasicoherentDerivedToDqcCompInclusion
    (R : CommRingCat.{u}) :
    affineQuasicoherentDerivedToDqc R ⋙
        SchemeQuasicoherentDerivedCategory.ι (Spec R) ≅
      affineQuasicoherentDerivedInclusion R :=
  (schemeQuasicoherentCohomology (Spec R)).liftCompιIso
    (affineQuasicoherentDerivedInclusion R)
    (affineQuasicoherentDerivedInclusion_mem_dqc R)

end

end CategoryTheory.Triangulated.StabilityCondition.Families
