/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.FullSubcategory
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Kernels

/-!
# Quasi-coherent module sheaves are closed under small coproducts

On an arbitrary scheme, a coproduct of quasi-coherent module sheaves is again
quasi-coherent, with no noetherian or quasi-compactness hypothesis and no bound
on the indexing type.

## The shape of the argument

The same two steps as `Kernels.lean`, and this is the *cheap* case there — the
one that needs no localization criterion:

1. Affine: `tilde` is a left adjoint, so it preserves the coproduct, and
   quasi-coherence of each `M i` says it already *is* a tilde. So `∐ M` is a
   tilde.
2. General: restriction along an open immersion is also a left adjoint, so it
   preserves the coproduct, and quasi-coherence is affine-local.

## What this is for

`ObjectProperty.IsClosedUnderColimitsOfShape (Discrete ι)` is what
`DerivedCategory.cohomologyIn_prop_coproduct` consumes on the abelian side, and
so is one of the two inputs `Dqc(X)`'s coproduct structure needs (#721).

**It is not the whole of that bullet.** The other input — that
`DerivedCategory X.Modules` *has* the coproducts and that every `Hⁿ` preserves
them — is absent from Mathlib at this pin and is not supplied here. Nothing in
this file asserts anything about the derived category.

The closure also gives the full subcategory of quasi-coherent sheaves its own
`ι`-indexed coproducts, with the inclusion into `X.Modules` **creating** them, so
a coproduct formed among quasi-coherent sheaves is the ambient one. That is the
compatibility a realization functor needs downstream, and it holds on an arbitrary
scheme. It says nothing about exactness of those coproducts: the subcategory is
not abelian on a general scheme, so AB4 for it is not even a statement here, and
where it is available (the affine case, through the tilde equivalence) it is
supplied by its own owner.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

namespace Scheme.Modules

/-! ### The affine case -/

variable {R : CommRingCat.{u}}

/-- **On an affine spectrum, a coproduct of quasi-coherent module sheaves is
quasi-coherent.**

`tilde` is a left adjoint, so it carries the coproduct of the `Γ(M i)` to the
coproduct of the `tilde Γ(M i)`, and quasi-coherence makes each `fromTildeΓ (M i)`
an isomorphism. Composing the two gives `∐ M` as a tilde. -/
theorem isQuasicoherent_sigma_affine {ι : Type u} (M : ι → (Spec R).Modules)
    (hM : ∀ i, (M i).IsQuasicoherent) : (∐ M).IsQuasicoherent := by
  letI := hM
  let e : (tilde.functor R).obj (∐ fun i ↦ moduleSpecΓFunctor.obj (M i)) ≅ ∐ M :=
    PreservesCoproduct.iso (tilde.functor R) _ ≪≫
      Sigma.mapIso (fun i ↦ @asIso _ _ _ _ (fromTildeΓ (M i))
        (isIso_fromTildeΓ_of_isQuasicoherent (M i)))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (inferInstanceAs (((tilde.functor R).obj
      (∐ fun i ↦ moduleSpecΓFunctor.obj (M i))).IsQuasicoherent))

/-! ### The general scheme -/

variable {X : Scheme.{u}}

/-- **Coproducts of quasi-coherent module sheaves are quasi-coherent**, on an
arbitrary scheme.

Restriction along an open immersion preserves coproducts, quasi-coherence is
affine-local, and the affine case applies on each member of
`X.affineOpenCover`. -/
theorem isQuasicoherent_sigma {ι : Type u} (M : ι → X.Modules)
    (hM : ∀ i, (M i).IsQuasicoherent) : (∐ M).IsQuasicoherent := by
  letI := hM
  let 𝒰 := X.affineOpenCover
  rw [isQuasicoherent_iff_restrict_affineOpenCover (∐ M) 𝒰]
  intro i
  have h : (∐ fun j ↦ (restrictFunctor (𝒰.f i)).obj (M j)).IsQuasicoherent :=
    isQuasicoherent_sigma_affine _ (fun j ↦ inferInstance)
  exact (SheafOfModules.isQuasicoherent (Spec (𝒰.X i)).ringCatSheaf).prop_of_iso
    (PreservesCoproduct.iso (restrictFunctor (𝒰.f i)) M).symm h

end Scheme.Modules

/-- **Quasi-coherence is closed under `ι`-indexed colimits of a discrete shape.**

This is the abelian-side input to `Dqc(X)`'s coproduct structure. Stated for one
indexing universe at a time, matching the repository's universe-explicit colimit
idiom rather than claiming closure under all colimits. -/
instance quasicoherent_isClosedUnderCoproducts (X : Scheme.{u}) (ι : Type u) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape
      (Discrete ι) :=
  ObjectProperty.IsClosedUnderColimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))).symm) ?_
    exact Scheme.Modules.isQuasicoherent_sigma _ (fun i ↦ hF ⟨i⟩))

/-- **The category of quasi-coherent sheaves has `ι`-indexed coproducts**, on an
arbitrary scheme.

Closure above plus the ambient coproducts is exactly what Mathlib's
`hasColimitsOfShape_of_closedUnderColimits` consumes. Nothing is transported and
no equivalence is used, so this holds with no hypothesis on `X`; in particular it
does not need quasi-coherent sheaves to be an abelian subcategory, which they are
not on a general scheme.

The instance is supplied by name rather than by `inferInstance` for the reason
recorded on `Dqc.SchemeQuasicoherentDerivedCategory.sigma_mem`: unifying the
ambient category with `X.Modules` routes it through `Scheme.Modules.instCategory`,
and search does not then match the instance's own head. Naming it is not a
workaround for an unproved fact -- it is the same instance, named. -/
instance quasicoherentSheaves_hasCoproductsOfShape (X : Scheme.{u}) (ι : Type u) :
    HasColimitsOfShape (Discrete ι)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  @Limits.hasColimitsOfShape_of_closedUnderColimits (Discrete ι) _ X.Modules _
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (quasicoherent_isClosedUnderCoproducts X ι) inferInstance

/-- **The inclusion of quasi-coherent sheaves preserves `ι`-indexed coproducts**,
on an arbitrary scheme.

This is the compatibility statement downstream consumers actually need: a
coproduct formed among quasi-coherent sheaves has the ambient coproduct as its
image, so a realization functor may compute either way.

The route is that closure makes the inclusion **create** those colimits
(Mathlib's `createsColimitsOfShapeFullSubcategoryInclusion`), which is strictly
stronger. Creation carries data rather than being a proposition, so it is used
here as a local term rather than exported as a second named declaration; a
consumer that needs it can rebuild it from
`quasicoherent_isClosedUnderCoproducts` in one line, as this proof does. -/
theorem quasicoherentSheavesInclusion_preservesCoproductsOfShape
    (X : Scheme.{u}) (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι := by
  haveI : CreatesColimitsOfShape (Discrete ι)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
    @Limits.createsColimitsOfShapeFullSubcategoryInclusion (Discrete ι) _ X.Modules _
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (quasicoherent_isClosedUnderCoproducts X ι) inferInstance
  infer_instance

/-- **The inclusion of quasi-coherent sheaves reflects `ι`-indexed coproducts**,
on an arbitrary scheme: a family in the subcategory whose ambient coproduct
cocone is a colimit was already a colimit there.  Creation again, in the form a
functor landing in the subcategory consumes. -/
theorem quasicoherentSheavesInclusion_reflectsCoproductsOfShape
    (X : Scheme.{u}) (ι : Type u) :
    ReflectsColimitsOfShape (Discrete ι)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι := by
  haveI : CreatesColimitsOfShape (Discrete ι)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
    @Limits.createsColimitsOfShapeFullSubcategoryInclusion (Discrete ι) _ X.Modules _
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (quasicoherent_isClosedUnderCoproducts X ι) inferInstance
  infer_instance

end

end AlgebraicGeometry
