/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.Localization.Kernels
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Affine.Comparison
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Descent.Locality
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Kernels and cokernels of coherent sheaves

On a locally noetherian scheme, coherent module sheaves are closed under kernels and
cokernels in the ambient category of module sheaves.

For kernels, the substantive affine input is that localization commutes with kernels.  Applied
to restriction from `Spec R` to every basic open, this identifies the ambient kernel with the
tilde sheaf of its global sections.  The global sections form a finite module because they are a
submodule of the finite global sections of the source over a noetherian ring.

For cokernels, tilde is a left adjoint and therefore preserves cokernels.  The affine comparison
counits identify the ambient cokernel with the tilde sheaf of the cokernel on global sections,
which is finite as a quotient of the finite global sections of the target.

The affine-local criterion then globalizes both results.  The final object-property instances
give `Coh X` kernels and cokernels through Mathlib's full-subcategory infrastructure.

## Main results

* `Scheme.Modules.restrictKernelIso` and `restrictCokernelIso` identify restriction of an
  ambient (co)kernel with the (co)kernel of the restricted morphism;
* `Scheme.Modules.isCoherent_kernel` and `isCoherent_cokernel` prove the object-level closure;
* `Scheme.coherent_isClosedUnderKernels` and `coherent_isClosedUnderCokernels` package the
  closure as object-property instances.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C) (F : A ⥤ B)
variable [HasFiniteLimits A] [HasFiniteLimits B]
variable [J.HasSheafCompose F] [PreservesFiniteLimits F]

private noncomputable instance whiskeringRightPreservesFiniteLimits :
    PreservesFiniteLimits ((Functor.whiskeringRight Cᵒᵖ A B).obj F) where
  preservesFiniteLimits _ _ _ :=
    { preservesLimit := fun {K} =>
        { preserves := fun {c} hc => ⟨by
            apply Limits.evaluationJointlyReflectsLimits
            intro k
            change IsLimit (((evaluation Cᵒᵖ A).obj k ⋙ F).mapCone c)
            exact isLimitOfPreserves _ hc⟩ } }

private noncomputable instance sheafComposePreservesFiniteLimits :
    PreservesFiniteLimits (sheafCompose J F) := by
  letI : PreservesFiniteLimits (sheafCompose J F ⋙ sheafToPresheaf J B) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J A ⋙ (Functor.whiskeringRight Cᵒᵖ A B).obj F)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J B)

end CategoryTheory

namespace PresheafOfModules

universe w

open CategoryTheory Limits

variable {C : Type w} [Category.{w} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
variable (X : Cᵒᵖ) (hX : IsInitial X)

private noncomputable instance forgetToPresheafModuleCatPreservesFiniteLimits :
    PreservesFiniteLimits (forgetToPresheafModuleCat X hX (R := R)) where
  preservesFiniteLimits J _ _ :=
    { preservesLimit := fun {K} => by
        apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
        apply CategoryTheory.Limits.evaluationJointlyReflectsLimits
        intro Y
        change IsLimit (((evaluation R Y ⋙
          ModuleCat.restrictScalars (R.map (hX.to Y)).hom).mapCone (limit.cone K)))
        exact isLimitOfPreserves _ (limit.isLimit K) }

end PresheafOfModules

namespace SheafOfModules

universe w

open CategoryTheory Limits

variable {C : Type w} [Category.{w} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}} (X : Cᵒᵖ) (hX : IsInitial X)

private noncomputable instance forgetToSheafModuleCatPreservesFiniteLimits :
    PreservesFiniteLimits (forgetToSheafModuleCat R X hX) := by
  letI : PreservesFiniteLimits
      (forgetToSheafModuleCat R X hX ⋙ sheafToPresheaf J (ModuleCat (R.obj.obj X))) := by
    change PreservesFiniteLimits
      (forget R ⋙ PresheafOfModules.forgetToPresheafModuleCat X hX)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf J (ModuleCat (R.obj.obj X)))

end SheafOfModules

namespace PresheafOfModules

universe w

open CategoryTheory Limits

variable {C D : Type w} [Category.{w} C] [Category.{w} D]
variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{w}} {S : Cᵒᵖ ⥤ RingCat.{w}}
variable (φ : S ⟶ F.op ⋙ R)

private noncomputable instance pushforwardPreservesFiniteLimits :
    PreservesFiniteLimits (pushforward.{w} φ) where
  preservesFiniteLimits J _ _ :=
    { preservesLimit := fun {K} => by
        apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
        apply evaluationJointlyReflectsLimits
        intro X
        change IsLimit (((evaluation R (F.op.obj X) ⋙
          ModuleCat.restrictScalars.{w} (φ.app X).hom).mapCone (limit.cone K)))
        exact isLimitOfPreserves _ (limit.isLimit K) }

end PresheafOfModules

namespace SheafOfModules

universe w

open CategoryTheory Limits

variable {C D : Type w} [Category.{w} C] [Category.{w} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
variable {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
variable [F.IsContinuous J K]
variable (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)

private noncomputable instance pushforwardPreservesFiniteLimits :
    PreservesFiniteLimits (pushforward.{w} φ) := by
  letI : PreservesFiniteLimits (pushforward.{w} φ ⋙ forget S) := by
    change PreservesFiniteLimits (forget R ⋙ PresheafOfModules.pushforward φ.hom)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget S)

end SheafOfModules

namespace AlgebraicGeometry

/-- The forgetful functor from module sheaves on `Spec R` to sheaves of `R`-modules preserves
finite limits. -/
noncomputable instance modulesSpecToSheaf_preservesFiniteLimits (R : CommRingCat.{u}) :
    PreservesFiniteLimits (modulesSpecToSheaf (R := R)) := by
  let hTop : IsInitial (Opposite.op (⊤ : (Spec R).Opens)) :=
    Limits.initialOpOfTerminal <| Limits.IsTerminal.ofUniqueHom
      (fun _ => homOfLE (fun _ _ => trivial)) (fun _ _ => Subsingleton.elim _ _)
  letI : PreservesFiniteLimits
      (sheafCompose (Opens.grothendieckTopology (Spec R))
        (ModuleCat.restrictScalars.{u} (StructureSheaf.globalSectionsIso R).hom.hom)) :=
    CategoryTheory.sheafComposePreservesFiniteLimits _ _
  change PreservesFiniteLimits
    (SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤) hTop ⋙
      sheafCompose _
        (ModuleCat.restrictScalars.{u} (StructureSheaf.globalSectionsIso R).hom.hom))
  constructor
  intro J _ _
  letI : PreservesLimitsOfShape J
      (SheafOfModules.forgetToSheafModuleCat (Spec R).ringCatSheaf (.op ⊤) hTop) :=
    inferInstance
  letI : PreservesLimitsOfShape J
      (sheafCompose (Opens.grothendieckTopology (Spec R))
        (ModuleCat.restrictScalars.{u} (StructureSheaf.globalSectionsIso R).hom.hom)) :=
    (CategoryTheory.sheafComposePreservesFiniteLimits
      (Opens.grothendieckTopology (Spec R))
      (ModuleCat.restrictScalars.{u}
        (StructureSheaf.globalSectionsIso R).hom.hom)).preservesFiniteLimits J
  exact
    { preservesLimit := fun {K} =>
        { preserves := fun {c} hc =>
            ⟨isLimitOfPreserves
              (sheafCompose (Opens.grothendieckTopology (Spec R))
                (ModuleCat.restrictScalars.{u}
                  (StructureSheaf.globalSectionsIso R).hom.hom))
              (isLimitOfPreserves
                (SheafOfModules.forgetToSheafModuleCat
                  (Spec R).ringCatSheaf (.op ⊤) hTop) hc)⟩ } }

/-- Scheme-level restriction along an open immersion preserves finite limits. -/
noncomputable instance Scheme.Modules.restrictFunctor_preservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) := by
  dsimp only [Scheme.Modules.restrictFunctor]
  exact SheafOfModules.pushforwardPreservesFiniteLimits _

variable {R : CommRingCat.{u}}

/-- Sections of an `𝒪_{Spec R}`-module over an open, as a functor to `R`-modules.

This is Mathlib's `moduleSpecΓFunctor` for a general open — and, at `U = ⊤`,
retyped. The retyping is the point: `moduleSpecΓFunctor` has domain
`(Spec (.of R)).Modules`, which is defeq to `(Spec R).Modules` but not to
instance search, so an instance proved for one is not found for the other.
Everything downstream states its geometry over `(Spec R).Modules`, so it wants
this one. `Modules/Affine/Equivalence.lean` records the same wrapper problem for
`Scheme.Modules` itself.

Public rather than private since #720: the quasi-coherent extension argument
needs `ShortComplex.map` through it, which means the instances below have to be
reachable from another file. -/
noncomputable def moduleSpecSectionsFunctor (R : CommRingCat.{u})
    (U : (Spec R).Opens) : (Spec R).Modules ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf ⋙
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op U))

/-- Sections over an open preserve finite limits. -/
noncomputable instance moduleSpecSectionsFunctor_preservesFiniteLimits
    (U : (Spec R).Opens) :
    PreservesFiniteLimits (moduleSpecSectionsFunctor R U) := by
  letI hModules : PreservesFiniteLimits (modulesSpecToSheaf (R := R)) :=
    modulesSpecToSheaf_preservesFiniteLimits R
  letI hForget : PreservesFiniteLimits
      (TopCat.Sheaf.forget (ModuleCat R) (Spec R)) := inferInstance
  letI hEval : PreservesFiniteLimits
      ((evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj (.op U)) := inferInstance
  let hForgetEval : PreservesFiniteLimits
      (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
        (evaluation (Opens (Spec R))ᵒᵖ (ModuleCat R)).obj (.op U)) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hForget hEval
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hModules hForgetEval

/-- Sections over an open preserve zero morphisms. -/
noncomputable instance moduleSpecSectionsFunctor_preservesZeroMorphisms
    (U : (Spec R).Opens) :
    (moduleSpecSectionsFunctor R U).PreservesZeroMorphisms := by
  infer_instance

private noncomputable def basicOpenRestrictionNatTrans (R : CommRingCat.{u}) (f : R) :
    moduleSpecSectionsFunctor R ⊤ ⟶
      moduleSpecSectionsFunctor R (PrimeSpectrum.basicOpen f) where
  app M := M.basicOpenRestriction f
  naturality _ _ φ := (Scheme.Modules.basicOpenRestriction_naturality φ f).symm

/-- Restriction to a basic open is a localization for the kernel of a morphism between
quasi-coherent module sheaves. -/
theorem Scheme.Modules.isLocalizedModule_basicOpenRestriction_kernel
    {M N : (Spec R).Modules} (g : M ⟶ N) (f : R)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    IsLocalizedModule (Submonoid.powers f) ((kernel g).basicOpenRestriction f).hom := by
  letI : IsLocalizedModule (Submonoid.powers f)
      ((basicOpenRestrictionNatTrans R f).app M).hom :=
    M.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent f
  letI : IsLocalizedModule (Submonoid.powers f)
      ((basicOpenRestrictionNatTrans R f).app N).hom :=
    N.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent f
  exact IsLocalizedModule.kernelNatTrans (Submonoid.powers f)
    (moduleSpecSectionsFunctor R ⊤)
    (moduleSpecSectionsFunctor R (PrimeSpectrum.basicOpen f))
    (basicOpenRestrictionNatTrans R f) g

/-- Kernels of morphisms between coherent module sheaves on an affine noetherian scheme are
coherent. -/
theorem Scheme.Modules.isCoherent_kernel_affine [IsNoetherianRing R]
    {M N : (Spec R).Modules} (g : M ⟶ N)
    (hM : M.IsCoherent) (hN : N.IsCoherent) : (kernel g).IsCoherent := by
  letI : SheafOfModules.IsFinitePresentation.{u, u, u} M := hM
  letI : SheafOfModules.IsFinitePresentation.{u, u, u} N := hN
  haveI (f : R) : IsLocalizedModule (Submonoid.powers f)
      ((kernel g).basicOpenRestriction f).hom :=
    Scheme.Modules.isLocalizedModule_basicOpenRestriction_kernel g f
  letI : IsIso (kernel g).fromTildeΓ :=
    (kernel g).isIso_fromTildeΓ_iff_isLocalizedModule.mpr fun _ => inferInstance
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    Scheme.Modules.moduleFinite_globalSections M hM
  letI : Module.Finite R
      (kernel (moduleSpecΓFunctor.map g) : ModuleCat.{u} R) :=
    Module.Finite.of_injective (kernel.ι (moduleSpecΓFunctor.map g)).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  letI : (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms := by
    change (moduleSpecSectionsFunctor R ⊤).PreservesZeroMorphisms
    infer_instance
  letI : PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) := by
    change PreservesFiniteLimits (moduleSpecSectionsFunctor R ⊤)
    infer_instance
  have hΓK : Module.Finite R
      ((moduleSpecΓFunctor (R := R)).obj (kernel g)) := by
    apply (Module.Finite.equiv_iff
      (PreservesKernel.iso (moduleSpecΓFunctor (R := R)) g).toLinearEquiv).mpr
    infer_instance
  letI := hΓK
  exact (Scheme.coherent (Spec R)).prop_of_iso
    (asIso (kernel g).fromTildeΓ)
    (isCoherent_tilde_of_finite (moduleSpecΓFunctor.obj (kernel g)))

/-- Cokernels of morphisms between coherent module sheaves on an affine noetherian scheme are
coherent. -/
theorem Scheme.Modules.isCoherent_cokernel_affine [IsNoetherianRing R]
    {M N : (Spec R).Modules} (g : M ⟶ N)
    (hM : M.IsCoherent) (hN : N.IsCoherent) : (cokernel g).IsCoherent := by
  letI : SheafOfModules.IsFinitePresentation.{u, u, u} M := hM
  letI : SheafOfModules.IsFinitePresentation.{u, u, u} N := hN
  letI : M.IsQuasicoherent := inferInstance
  letI : N.IsQuasicoherent := inferInstance
  letI hMIso : IsIso M.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  letI hNIso : IsIso N.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  letI : Module.Finite R (moduleSpecΓFunctor.obj N) :=
    Scheme.Modules.moduleFinite_globalSections N hN
  letI : Module.Finite R
      (cokernel (moduleSpecΓFunctor.map g) : ModuleCat.{u} R) :=
    Module.Finite.of_surjective (cokernel.π (moduleSpecΓFunctor.map g)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  let e : tilde (cokernel (moduleSpecΓFunctor.map g)) ≅ cokernel g :=
    PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map g) ≪≫
      cokernel.mapIso ((tilde.functor R).map (moduleSpecΓFunctor.map g)) g
        (@asIso _ _ _ _ M.fromTildeΓ hMIso)
        (@asIso _ _ _ _ N.fromTildeΓ hNIso)
        ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality g)
  exact (Scheme.coherent (Spec R)).prop_of_iso e
    (isCoherent_tilde_of_finite (cokernel (moduleSpecΓFunctor.map g)))

/-- Restriction along an open immersion commutes with kernels. -/
noncomputable def Scheme.Modules.restrictKernelIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (g : M ⟶ N) :
    (kernel g).restrict f ≅ kernel ((Scheme.Modules.restrictFunctor f).map g) :=
  PreservesKernel.iso (Scheme.Modules.restrictFunctor f) g

/-- Restriction along an open immersion commutes with cokernels. -/
noncomputable def Scheme.Modules.restrictCokernelIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (g : M ⟶ N) :
    (cokernel g).restrict f ≅ cokernel ((Scheme.Modules.restrictFunctor f).map g) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) g

variable {X : Scheme.{u}}

/-- Kernels of morphisms between coherent module sheaves on a locally noetherian scheme are
coherent. -/
theorem Scheme.Modules.isCoherent_kernel [IsLocallyNoetherian X]
    {M N : X.Modules} (g : M ⟶ N) (hM : M.IsCoherent) (hN : N.IsCoherent) :
    (kernel g).IsCoherent := by
  let 𝒰 := X.affineOpenCover
  rw [Scheme.Modules.isCoherent_iff_restrict_affineOpenCover (kernel g) 𝒰]
  intro i
  letI : IsLocallyNoetherian (Spec (𝒰.X i)) :=
    isLocallyNoetherian_of_isOpenImmersion (𝒰.f i)
  letI : IsNoetherianRing (𝒰.X i) := isLocallyNoetherian_Spec.mp inferInstance
  have hMi := Scheme.Modules.IsCoherent.restrict_affineOpenCover M 𝒰 hM i
  have hNi := Scheme.Modules.IsCoherent.restrict_affineOpenCover N 𝒰 hN i
  have hKi := Scheme.Modules.isCoherent_kernel_affine
    ((Scheme.Modules.restrictFunctor (𝒰.f i)).map g) hMi hNi
  exact (Scheme.coherent (Spec (𝒰.X i))).prop_of_iso
    (Scheme.Modules.restrictKernelIso (𝒰.f i) g).symm hKi

/-- Cokernels of morphisms between coherent module sheaves on a locally noetherian scheme are
coherent. -/
theorem Scheme.Modules.isCoherent_cokernel [IsLocallyNoetherian X]
    {M N : X.Modules} (g : M ⟶ N) (hM : M.IsCoherent) (hN : N.IsCoherent) :
    (cokernel g).IsCoherent := by
  let 𝒰 := X.affineOpenCover
  rw [Scheme.Modules.isCoherent_iff_restrict_affineOpenCover (cokernel g) 𝒰]
  intro i
  letI : IsLocallyNoetherian (Spec (𝒰.X i)) :=
    isLocallyNoetherian_of_isOpenImmersion (𝒰.f i)
  letI : IsNoetherianRing (𝒰.X i) := isLocallyNoetherian_Spec.mp inferInstance
  have hMi := Scheme.Modules.IsCoherent.restrict_affineOpenCover M 𝒰 hM i
  have hNi := Scheme.Modules.IsCoherent.restrict_affineOpenCover N 𝒰 hN i
  have hQi := Scheme.Modules.isCoherent_cokernel_affine
    ((Scheme.Modules.restrictFunctor (𝒰.f i)).map g) hMi hNi
  exact (Scheme.coherent (Spec (𝒰.X i))).prop_of_iso
    (Scheme.Modules.restrictCokernelIso (𝒰.f i) g).symm hQi

/-- Coherent module sheaves on a locally noetherian scheme are closed under kernels in the
ambient module-sheaf category. -/
noncomputable instance Scheme.coherent_isClosedUnderKernels [IsLocallyNoetherian X] :
    (Scheme.coherent X).IsClosedUnderKernels where
  kernels_le := by
    rintro K ⟨g, k, hk, hMN⟩
    rcases hMN with ⟨hM, hN⟩
    let e : k.pt ≅ kernel g := IsLimit.conePointUniqueUpToIso hk (limit.isLimit _)
    exact (Scheme.coherent X).prop_of_iso e.symm
      (Scheme.Modules.isCoherent_kernel g hM hN)

/-- Coherent module sheaves on a locally noetherian scheme are closed under cokernels in the
ambient module-sheaf category. -/
noncomputable instance Scheme.coherent_isClosedUnderCokernels [IsLocallyNoetherian X] :
    (Scheme.coherent X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro Q ⟨g, q, hq, hMN⟩
    rcases hMN with ⟨hM, hN⟩
    let e : q.pt ≅ cokernel g := IsColimit.coconePointUniqueUpToIso hq (colimit.isColimit _)
    exact (Scheme.coherent X).prop_of_iso e.symm
      (Scheme.Modules.isCoherent_cokernel g hM hN)

end AlgebraicGeometry
