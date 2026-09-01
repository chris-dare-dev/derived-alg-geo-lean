/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Abelian.Kernels
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Descent.Locality

/-!
# Quasi-coherent module sheaves are closed under kernels and cokernels

On an arbitrary scheme, an ambient kernel or cokernel of a morphism between
quasi-coherent module sheaves is again quasi-coherent. This is the half of the
weak Serre property that does not need extensions, and it is what makes the
inclusion of quasi-coherent sheaves into all module sheaves exact.

## Why this file exists at this layer

The affine case was previously proved inside the moduli lane, in
`DerivedCategory/Dqc/AffineRealization.lean`, where it was reachable
only by that lane. Quasi-coherence closure is a general fact about schemes: the
Serre lane wants it, and `Dqc(X)`'s triangulated structure wants it. So it lives
here, under `AlgebraicGeometry`, and the moduli lane consumes it.

## The shape of the argument

Exactly the shape `Abelian/Kernels.lean` uses for coherence, with the Noetherian
hypotheses deleted — quasi-coherence needs none.

1. Affine: a kernel is quasi-coherent because its basic-open restrictions are
   localizations (`isLocalizedModule_basicOpenRestriction_kernel`), which is the
   `fromTildeΓ` criterion. A cokernel is quasi-coherent because `tilde` is a left
   adjoint, so it preserves the cokernel, and both ends are already tildes.
2. General: restriction along an open immersion preserves finite limits and
   colimits, and quasi-coherence is affine-local, so the affine case transfers
   along `X.affineOpenCover`.

## Main results

* `Scheme.Hom.isQuasicoherent_over_iff_restrict`;
* `Scheme.Modules.isQuasicoherent_iff_restrict_affineOpenCover`;
* `Scheme.Modules.isQuasicoherent_kernel` and `isQuasicoherent_cokernel`;
* `Scheme.quasicoherent_isClosedUnderKernels` and
  `Scheme.quasicoherent_isClosedUnderCokernels`.
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-! ### The open-immersion/slice bridge -/

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Quasi-coherence after scheme-level restriction along an open immersion implies
quasi-coherence on the range slice — the converse of the `restrictFunctor`
instance. -/
theorem isQuasicoherent_over_of_restrict (M : Y.Modules)
    (hM : (M.restrict f).IsQuasicoherent) :
    (M.over f.opensRange).IsQuasicoherent := by
  obtain ⟨q⟩ := hM.nonempty_quasicoherentData
  exact (f.overQuasicoherentData M q).isQuasicoherent

/-- Quasi-coherence on the range slice implies quasi-coherence after scheme-level
restriction. -/
theorem isQuasicoherent_restrict (M : Y.Modules)
    (hM : (M.over f.opensRange).IsQuasicoherent) :
    (M.restrict f).IsQuasicoherent := by
  obtain ⟨q⟩ := hM.nonempty_quasicoherentData
  exact (f.restrictQuasicoherentData M q).isQuasicoherent

/-- **Quasi-coherence is invariant under the open-immersion/slice equivalence.**

The mirror of `isFinitePresentation_over_iff_restrict`, and it is cheaper: the
two transport maps `overQuasicoherentData` and `restrictQuasicoherentData`
already exist for the finite-presentation proof, and quasi-coherence is what is
left of that statement once the finiteness fields are dropped. -/
theorem isQuasicoherent_over_iff_restrict (M : Y.Modules) :
    (M.over f.opensRange).IsQuasicoherent ↔ (M.restrict f).IsQuasicoherent :=
  ⟨f.isQuasicoherent_restrict M, f.isQuasicoherent_over_of_restrict M⟩

end Scheme.Hom

/-! ### The affine-local criterion -/

namespace Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules)
  (𝒰 : AlgebraicGeometry.Scheme.AffineOpenCover.{u, u} X)

/-- Quasi-coherence descends from the range slices of an affine open cover. -/
theorem isQuasicoherent_of_affineOpenCover
    (h : ∀ i : 𝒰.I₀, (M.over ((𝒰.f i).opensRange)).IsQuasicoherent) :
    M.IsQuasicoherent := by
  letI : ∀ i : 𝒰.I₀, (M.over ((𝒰.f i).opensRange)).IsQuasicoherent := h
  refine SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun i ↦ (𝒰.f i).opensRange) ?_
  apply TopCat.Opens.grothendieckTopology_coversTop
  exact 𝒰.openCover.iSup_opensRange

/-- **The scheme-level affine-local criterion for quasi-coherence.**

Stated against scheme-level restriction rather than the range slice, so that
downstream arguments never have to mention `Over` or `M.over`. -/
theorem isQuasicoherent_iff_restrict_affineOpenCover :
    M.IsQuasicoherent ↔ ∀ i : 𝒰.I₀, (M.restrict (𝒰.f i)).IsQuasicoherent := by
  constructor
  · intro hM i
    letI : M.IsQuasicoherent := hM
    infer_instance
  · intro h
    refine isQuasicoherent_of_affineOpenCover M 𝒰 fun i ↦ ?_
    exact ((𝒰.f i).isQuasicoherent_over_iff_restrict M).mpr (h i)

end Scheme.Modules

/-! ### The affine case -/

namespace Scheme.Modules

variable {R : CommRingCat.{u}}

/-- On an affine spectrum, an ambient kernel of a morphism between quasi-coherent
module sheaves is quasi-coherent.

The criterion is `fromTildeΓ`: a module sheaf on `Spec R` is quasi-coherent
exactly when its basic-open restrictions are the corresponding localizations, and
`isLocalizedModule_basicOpenRestriction_kernel` says a kernel inherits that from
its two ends. No Noetherian hypothesis appears, and none is needed. -/
theorem isQuasicoherent_kernel_affine
    {M N : (Spec R).Modules} (g : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (kernel g).IsQuasicoherent := by
  letI : M.IsQuasicoherent := hM
  letI : N.IsQuasicoherent := hN
  haveI (f : R) : IsLocalizedModule (Submonoid.powers f)
      (Scheme.Modules.basicOpenRestriction (kernel g) f).hom :=
    Scheme.Modules.isLocalizedModule_basicOpenRestriction_kernel g f
  letI : IsIso (Scheme.Modules.fromTildeΓ (kernel g)) :=
    (Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule (kernel g)).mpr
      fun _ ↦ inferInstance
  exact (isQuasicoherent_iff_isIso_fromTildeΓ (kernel g)).mpr inferInstance

/-- On an affine spectrum, an ambient cokernel of a morphism between quasi-coherent
module sheaves is quasi-coherent.

Cheaper than the kernel: `tilde` is a left adjoint, so it already preserves the
cokernel, and quasi-coherence of the two ends says they *are* tildes. -/
theorem isQuasicoherent_cokernel_affine
    {M N : (Spec R).Modules} (g : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (cokernel g).IsQuasicoherent := by
  letI : M.IsQuasicoherent := hM
  letI : N.IsQuasicoherent := hN
  letI hMIso : IsIso (Scheme.Modules.fromTildeΓ M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  letI hNIso : IsIso (Scheme.Modules.fromTildeΓ N) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let e : tilde (cokernel (moduleSpecΓFunctor.map g)) ≅ cokernel g :=
    PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map g) ≪≫
      cokernel.mapIso ((tilde.functor R).map (moduleSpecΓFunctor.map g)) g
        (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ M) hMIso)
        (@asIso _ _ _ _ (Scheme.Modules.fromTildeΓ N) hNIso)
        ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality g)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    inferInstance

end Scheme.Modules

/-! ### The general scheme -/

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- **Kernels of morphisms between quasi-coherent module sheaves are
quasi-coherent**, on an arbitrary scheme.

Restriction along an open immersion preserves finite limits, so the kernel
restricts to a kernel; quasi-coherence is affine-local; and the affine case
applies on each member of `X.affineOpenCover`. -/
theorem isQuasicoherent_kernel {M N : X.Modules} (g : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (kernel g).IsQuasicoherent := by
  letI : M.IsQuasicoherent := hM
  letI : N.IsQuasicoherent := hN
  let 𝒰 := X.affineOpenCover
  rw [Scheme.Modules.isQuasicoherent_iff_restrict_affineOpenCover (kernel g) 𝒰]
  intro i
  have hKi := Scheme.Modules.isQuasicoherent_kernel_affine
    ((Scheme.Modules.restrictFunctor (𝒰.f i)).map g) inferInstance inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec (𝒰.X i)).ringCatSheaf).prop_of_iso
    (Scheme.Modules.restrictKernelIso (𝒰.f i) g).symm hKi

/-- **Cokernels of morphisms between quasi-coherent module sheaves are
quasi-coherent**, on an arbitrary scheme. -/
theorem isQuasicoherent_cokernel {M N : X.Modules} (g : M ⟶ N)
    (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    (cokernel g).IsQuasicoherent := by
  letI : M.IsQuasicoherent := hM
  letI : N.IsQuasicoherent := hN
  let 𝒰 := X.affineOpenCover
  rw [Scheme.Modules.isQuasicoherent_iff_restrict_affineOpenCover (cokernel g) 𝒰]
  intro i
  have hQi := Scheme.Modules.isQuasicoherent_cokernel_affine
    ((Scheme.Modules.restrictFunctor (𝒰.f i)).map g) inferInstance inferInstance
  exact (SheafOfModules.isQuasicoherent (Spec (𝒰.X i)).ringCatSheaf).prop_of_iso
    (Scheme.Modules.restrictCokernelIso (𝒰.f i) g).symm hQi

end Scheme.Modules

/-! ### Closure, as an `ObjectProperty` -/

variable (X : Scheme.{u})

/-- Quasi-coherent module sheaves on an arbitrary scheme are closed under ambient
kernels. -/
instance quasicoherent_isClosedUnderKernels :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro K ⟨g, k, hk, hM, hN⟩
    let e : k.pt ≅ kernel g := IsLimit.conePointUniqueUpToIso hk (limit.isLimit _)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
      (Scheme.Modules.isQuasicoherent_kernel g hM hN)

/-- Quasi-coherent module sheaves on an arbitrary scheme are closed under ambient
cokernels. -/
instance quasicoherent_isClosedUnderCokernels :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro Q ⟨g, q, hq, hM, hN⟩
    let e : q.pt ≅ cokernel g := IsColimit.coconePointUniqueUpToIso hq (colimit.isColimit _)
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
      (Scheme.Modules.isQuasicoherent_cokernel g hM hN)

end

end AlgebraicGeometry
