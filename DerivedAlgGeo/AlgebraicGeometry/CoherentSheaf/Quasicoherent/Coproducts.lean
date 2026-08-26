/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Quasicoherent.Kernels

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

end

end AlgebraicGeometry
