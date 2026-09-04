/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Subobject.ArtinianObject
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Strict morphisms, and finiteness conditions built from them

A morphism is **strict** when its canonical coimage-to-image comparison is an
isomorphism.  The universal-property criteria below avoid importing the
corresponding vendor module.

Four layers, in order:

* strict morphisms — `IsStrict`, `IsStrictMono`, `IsStrictEpi`, their kernel
  and cokernel criteria, and their relation to `NormalMono`/`RegularEpi`/
  `StrongEpi`;
* `StrictShortExact`, and what it becomes in an abelian category, where every
  morphism is strict (`isStrict_of_abelian`);
* strict subobjects, and the strict Artinian, Noetherian and finite-length
  object properties they generate, each paired with its non-strict counterpart;
* transfer of all of it along a fully faithful functor preserving monos.

## Placement

Generic category theory: this file imports only Mathlib's abelian, short-complex,
pullback, and subobject material, mentions no stability condition, and uses
nothing triangulated. It lives under `CategoryTheory/Abelian/`, beside Mathlib's
`Abelian/NonPreadditive.lean` precedent for a category with exactness conditions
weaker than abelian. It sat under `StabilityCondition/Foundation/` until #488
because its first consumer was Bridgeland's thin-interval argument
(`Foundation/Slicing/IntervalStrictness.lean` is still the caller), then under
`Triangulated/` until 2026-09-02, when the review of the Mathlib-mesh restructure
applied the rule that a file belongs under `Triangulated/` only if it uses
something triangulated. The namespace stays `CategoryTheory.Triangulated`:
declaration names are unchanged across moves so that the immutable review
payloads the `exe/RestateHistoricalNames.lean` bridge protects keep resolving.

## What this file asserts, and where

The `QuasiAbelian` class below states the two stability axioms — strict
epimorphisms stable under pullback, strict monomorphisms stable under pushout.
It is inhabited: `Slicing.intervalCat_quasiAbelian`
(`Foundation/Slicing/IntervalStrictness.lean`) shows a thin owner slicing
interval is quasi-abelian, and it is the only instance at the time of writing.

Most of the file is prior to that class: strictness of individual morphisms and
the finiteness conditions built on it, none of which needs the axioms.

Two earlier versions of this section were wrong, in opposite directions. The
first said `QuasiAbelian` "appears in no declaration in this file", which the
class below contradicts. Its replacement said no category is shown to be
quasi-abelian, which `intervalCat_quasiAbelian` contradicts — the search behind
that claim matched one line at a time, and the instance carries its type on the
next line. Neither claim should have been made without a search that could see
a multi-line signature.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section

variable {X Y : C} (f : X ⟶ Y)
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- A morphism is strict when the canonical coimage-to-image comparison is
an isomorphism. -/
def IsStrict : Prop :=
  IsIso (Abelian.coimageImageComparison f)

/-- A strict monomorphism. -/
structure IsStrictMono : Prop where
  mono : Mono f
  strict : IsStrict f

/-- A strict epimorphism. -/
structure IsStrictEpi : Prop where
  epi : Epi f
  strict : IsStrict f

end

section

variable {X Y : C} {f : X ⟶ Y} [HasZeroObject C]
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- A morphism which is the cokernel of its kernel is a strict epimorphism. -/
theorem isStrictEpi_of_isColimitCokernelCofork
    (hf : IsColimit (CokernelCofork.ofπ f (kernel.condition f))) :
    IsStrictEpi f := by
  haveI : Epi f := Cofork.IsColimit.epi hf
  let e : Abelian.coimage f ≅ Y :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι f)) hf
  have he : Abelian.coimage.π f ≫ e.hom = f := by
    have he' := IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (kernel.ι f)) hf Limits.WalkingParallelPair.one
    dsimp [Abelian.coimage, e, CokernelCofork.ofπ] at he'
    exact he'
  have hcomp : Abelian.coimageImageComparison f ≫ Abelian.image.ι f = e.hom := by
    apply (cancel_epi (Abelian.coimage.π f)).1
    rw [he]
    exact Abelian.coimage_image_factorisation (f := f)
  refine ⟨inferInstance, ?_⟩
  letI : IsIso (Abelian.image.ι f) := kernel.of_cokernel_of_epi (f := f)
  letI : Mono (Abelian.image.ι f) := by infer_instance
  change IsIso (Abelian.coimageImageComparison f)
  rw [show Abelian.coimageImageComparison f = e.hom ≫ inv (Abelian.image.ι f) from by
    apply (cancel_mono (Abelian.image.ι f)).1
    simpa [Abelian.image] using hcomp]
  infer_instance

/-- A morphism which is the kernel of its cokernel is a strict monomorphism. -/
theorem isStrictMono_of_isLimitKernelFork
    (hf : IsLimit (KernelFork.ofι f (cokernel.condition f))) :
    IsStrictMono f := by
  haveI : Mono f := Fork.IsLimit.mono hf
  have hker : IsLimit
      (KernelFork.ofι (Abelian.image.ι f)
        (kernel.condition (cokernel.π f))) := by
    simpa [Abelian.image, KernelFork.ofι] using
      (kernelIsKernel (cokernel.π f))
  let u : X ⟶ Abelian.image f :=
    hker.lift (KernelFork.ofι f (cokernel.condition f))
  have hu : u ≫ Abelian.image.ι f = f :=
    hker.fac (KernelFork.ofι f (cokernel.condition f))
      Limits.WalkingParallelPair.zero
  let w : Abelian.image f ⟶ X :=
    hf.lift (KernelFork.ofι (Abelian.image.ι f)
      (kernel.condition (cokernel.π f)))
  have hw : w ≫ f = Abelian.image.ι f :=
    hf.fac (KernelFork.ofι (Abelian.image.ι f)
      (kernel.condition (cokernel.π f))) Limits.WalkingParallelPair.zero
  let e : X ≅ Abelian.image f :=
    ⟨u, w, by
      apply (cancel_mono f).1
      rw [Category.assoc, hw, hu]
      simp, by
      apply (cancel_mono (Abelian.image.ι f)).1
      rw [Category.assoc, hu, hw]
      simp⟩
  have he : e.hom ≫ Abelian.image.ι f = f := hu
  have hcomp : Abelian.coimage.π f ≫
      Abelian.coimageImageComparison f = e.hom := by
    apply (cancel_mono (Abelian.image.ι f)).1
    rw [he]
    rw [Category.assoc]
    exact Abelian.coimage_image_factorisation (f := f)
  refine ⟨inferInstance, ?_⟩
  letI : IsIso (Abelian.coimage.π f) := cokernel.of_kernel_of_mono (f := f)
  letI : Epi (Abelian.coimage.π f) := by infer_instance
  letI : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  change IsIso (Abelian.coimageImageComparison f)
  rw [show Abelian.coimageImageComparison f = inv (Abelian.coimage.π f) ≫ e.hom from by
    apply (cancel_epi (Abelian.coimage.π f)).1
    simpa [Abelian.image] using hcomp]
  infer_instance

/-- A strict epimorphism is the cokernel of its kernel. -/
noncomputable def IsStrictEpi.isColimitCokernelCofork
    (hf : IsStrictEpi f) :
    IsColimit (CokernelCofork.ofπ f (kernel.condition f)) := by
  letI : Epi f := hf.epi
  letI : IsIso (Abelian.coimageImageComparison f) := hf.strict
  letI : IsIso (kernel.ι (cokernel.π f)) :=
    kernel.of_cokernel_of_epi (f := f)
  let e : cokernel (kernel.ι f) ≅ Y :=
    asIso (Abelian.coimageImageComparison f ≫ kernel.ι (cokernel.π f))
  have hm : cokernel.π (kernel.ι f) ≫ e.hom = f := by
    change cokernel.π (kernel.ι f) ≫ Abelian.coimageImageComparison f ≫
      kernel.ι (cokernel.π f) = f
    exact Abelian.coimage_image_factorisation (f := f)
  exact cokernel.cokernelIso (kernel.ι f) f e hm

/-- A strict monomorphism is the kernel of its cokernel. -/
noncomputable def IsStrictMono.isLimitKernelFork
    (hf : IsStrictMono f) :
    IsLimit (KernelFork.ofι f (cokernel.condition f)) := by
  letI : Mono f := hf.mono
  letI : IsIso (Abelian.coimageImageComparison f) := hf.strict
  letI : IsIso (cokernel.π (kernel.ι f)) :=
    cokernel.of_kernel_of_mono (f := f)
  let e : X ≅ kernel (cokernel.π f) :=
    asIso (cokernel.π (kernel.ι f) ≫ Abelian.coimageImageComparison f)
  have hm : e.hom ≫ kernel.ι (cokernel.π f) = f := by
    dsimp [e]
    rw [Category.assoc]
    exact Abelian.coimage_image_factorisation (f := f)
  exact kernel.isoKernel (cokernel.π f) f e hm

/-- A strict epimorphism supplies a normal epimorphism witness. -/
@[reducible]
noncomputable def IsStrictEpi.normalEpi (hf : IsStrictEpi f) : NormalEpi f where
  W := kernel f
  g := kernel.ι f
  w := kernel.condition f
  isColimit := hf.isColimitCokernelCofork

/-- A strict monomorphism supplies a normal monomorphism witness. -/
@[reducible]
noncomputable def IsStrictMono.normalMono (hf : IsStrictMono f) : NormalMono f where
  Z := cokernel f
  g := cokernel.π f
  w := cokernel.condition f
  isLimit := hf.isLimitKernelFork

/-- Every isomorphism is a strict monomorphism. -/
theorem isStrictMono_of_isIso [IsIso f] : IsStrictMono f := by
  apply isStrictMono_of_isLimitKernelFork
  have hk : cokernel.π f = 0 := (isZero_cokernel_of_epi f).eq_of_tgt _ _
  refine KernelFork.IsLimit.ofι' f (by simp [hk]) (fun {A} k _ ↦ ?_)
  exact ⟨k ≫ inv f, by simp [Category.assoc]⟩

/-- Every isomorphism is a strict epimorphism. -/
theorem isStrictEpi_of_isIso [IsIso f] : IsStrictEpi f := by
  apply isStrictEpi_of_isColimitCokernelCofork
  have hk : kernel.ι f = 0 := (isZero_kernel_of_mono f).eq_of_src _ _
  refine CokernelCofork.IsColimit.ofπ' f (by simp [hk]) (fun {A} k _ ↦ ?_)
  exact ⟨inv f ≫ k, by simp⟩

/-- A strict epimorphism which is also monic is an isomorphism. -/
theorem IsStrictEpi.isIso (hf : IsStrictEpi f) [Mono f] : IsIso f := by
  letI : Epi f := hf.epi
  have hk : kernel.ι f = 0 := (isZero_kernel_of_mono f).eq_of_src _ _
  let s : Y ⟶ X :=
    hf.isColimitCokernelCofork.desc
      (CokernelCofork.ofπ (𝟙 X) (by simp [hk]))
  have hs : f ≫ s = 𝟙 X :=
    hf.isColimitCokernelCofork.fac
      (CokernelCofork.ofπ (𝟙 X) (by simp [hk]))
      Limits.WalkingParallelPair.one
  letI : IsSplitMono f := IsSplitMono.mk' ⟨s, hs⟩
  exact isIso_of_epi_of_isSplitMono f

/-- A strict monomorphism which is also epic is an isomorphism. -/
theorem IsStrictMono.isIso (hf : IsStrictMono f) [Epi f] : IsIso f := by
  letI : Mono f := hf.mono
  have hk : cokernel.π f = 0 := (isZero_cokernel_of_epi f).eq_of_tgt _ _
  let s : Y ⟶ X :=
    hf.isLimitKernelFork.lift
      (KernelFork.ofι (𝟙 Y) (by simp [hk]))
  have hs : s ≫ f = 𝟙 Y :=
    hf.isLimitKernelFork.fac
      (KernelFork.ofι (𝟙 Y) (by simp [hk]))
      Limits.WalkingParallelPair.zero
  letI : IsSplitEpi f := IsSplitEpi.mk' ⟨s, hs⟩
  exact isIso_of_mono_of_isSplitEpi f

/-- Every normal epimorphism is strict. -/
theorem isStrictEpi_of_normalEpi [hf : NormalEpi f] : IsStrictEpi f := by
  let g' : hf.W ⟶ kernel f := kernel.lift f hf.g hf.w
  have hcolim : IsColimit (CokernelCofork.ofπ f (kernel.condition f)) :=
    isCokernelOfComp (f := kernel.ι f) g' hf.g hf.isColimit
      (kernel.condition f) (kernel.lift_ι f hf.g hf.w)
  exact isStrictEpi_of_isColimitCokernelCofork hcolim

/-- Every normal monomorphism is strict. -/
theorem isStrictMono_of_normalMono [hf : NormalMono f] : IsStrictMono f := by
  let g' : cokernel f ⟶ hf.Z := cokernel.desc f hf.g hf.w
  have hlim : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    isKernelOfComp (f := cokernel.π f) g' hf.g hf.isLimit
      (cokernel.condition f) (cokernel.π_desc f hf.g hf.w)
  exact isStrictMono_of_isLimitKernelFork hlim

/-- A strict epimorphism supplies a regular epimorphism witness. -/
noncomputable def IsStrictEpi.regularEpi (hf : IsStrictEpi f) : RegularEpi f :=
  hf.normalEpi.regularEpi f

/-- Every strict epimorphism is strong. -/
theorem IsStrictEpi.strongEpi (hf : IsStrictEpi f) : StrongEpi f := by
  have := isRegularEpi_of_regularEpi hf.regularEpi
  infer_instance

/-- A strict monomorphism supplies a regular monomorphism witness. -/
noncomputable def IsStrictMono.regularMono (hf : IsStrictMono f) : RegularMono f :=
  hf.normalMono.regularMono f

/-- Every strict monomorphism is strong. -/
theorem IsStrictMono.strongMono (hf : IsStrictMono f) : StrongMono f := by
  have := isRegularMono_of_regularMono hf.regularMono
  infer_instance

end

section

variable [HasKernels C] [HasCokernels C]

/-- A kernel inclusion is a strict monomorphism. -/
theorem isStrictMono_kernel {X Y : C} (g : X ⟶ Y) :
    IsStrictMono (kernel.ι g) where
  mono := inferInstance
  strict := by
    have hk0 : kernel.ι (kernel.ι g) =
        (0 : kernel (kernel.ι g) ⟶ kernel g) :=
      (isZero_kernel_of_mono (kernel.ι g)).eq_zero_of_src _
    haveI : IsIso (cokernel.π (kernel.ι (kernel.ι g))) := by
      rw [hk0]
      infer_instance
    have hfactor : kernel.ι (cokernel.π (kernel.ι g)) ≫ g = 0 := by
      have hf := cokernel.π_desc (kernel.ι g) g (kernel.condition g)
      conv_lhs => rhs; rw [← hf]
      rw [← Category.assoc, kernel.condition, zero_comp]
    have hℓj : kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _) ≫
        kernel.lift g (kernel.ι (cokernel.π (kernel.ι g))) hfactor = 𝟙 _ := by
      ext
      simp
    have hjℓ : kernel.lift g (kernel.ι (cokernel.π (kernel.ι g))) hfactor ≫
        kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _) = 𝟙 _ := by
      ext
      simp
    haveI : IsIso
        (kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _)) := ⟨⟨_, hℓj, hjℓ⟩⟩
    change IsIso (Abelian.coimageImageComparison (kernel.ι g))
    have hπ : cokernel.π (kernel.ι (kernel.ι g)) ≫
        Abelian.coimageImageComparison (kernel.ι g) =
        kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _) :=
      cokernel.π_desc _ _ _
    rw [show Abelian.coimageImageComparison (kernel.ι g) =
        inv (cokernel.π (kernel.ι (kernel.ι g))) ≫
          kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
            (cokernel.condition _) from by
      rw [← hπ, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]]
    infer_instance

/-- A cokernel projection is a strict epimorphism. -/
theorem isStrictEpi_cokernel {X Y : C} (g : X ⟶ Y) :
    IsStrictEpi (cokernel.π g) where
  epi := inferInstance
  strict := by
    have hc0 : cokernel.π (cokernel.π g) =
        (0 : cokernel g ⟶ cokernel (cokernel.π g)) :=
      (isZero_cokernel_of_epi (cokernel.π g)).eq_zero_of_tgt _
    haveI : IsIso (kernel.ι (cokernel.π (cokernel.π g))) := by
      rw [hc0]
      infer_instance
    have hfactor : g ≫ cokernel.π (kernel.ι (cokernel.π g)) = 0 := by
      rw [← Abelian.coimage_image_factorisation_assoc g]
      simp
    have hhk : cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) ≫
        cokernel.desc g (cokernel.π (kernel.ι (cokernel.π g))) hfactor = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (kernel.ι (cokernel.π g)))).mp
      simp
    have hkh : cokernel.desc g (cokernel.π (kernel.ι (cokernel.π g))) hfactor ≫
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) = 𝟙 _ := by
      apply (cancel_epi (cokernel.π g)).mp
      simp
    haveI : IsIso
        (cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _)) := ⟨⟨_, hhk, hkh⟩⟩
    change IsIso (Abelian.coimageImageComparison (cokernel.π g))
    have hcomp : Abelian.coimageImageComparison (cokernel.π g) ≫
        kernel.ι (cokernel.π (cokernel.π g)) =
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) := by
      apply (cancel_epi (cokernel.π (kernel.ι (cokernel.π g)))).mp
      simp
    rw [show Abelian.coimageImageComparison (cokernel.π g) =
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) ≫
          inv (kernel.ι (cokernel.π (cokernel.π g))) from by
      rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    infer_instance

end

section

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasKernels C] [HasCokernels C] [HasPullbacks C] [HasPushouts C]

/-- An owner quasi-abelian category is preabelian and has pullbacks and
pushouts, with strict epimorphisms stable under pullback and strict
monomorphisms stable under pushout. -/
class QuasiAbelian : Prop where
  pullback_strictEpi : ∀ {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    IsStrictEpi g → IsStrictEpi (pullback.fst f g)
  pushout_strictMono : ∀ {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y),
    IsStrictMono f → IsStrictMono (pushout.inr f g)

end

section

variable [HasKernels C] [HasCokernels C]

/-- A strict short exact sequence is a short exact complex whose two maps are
strict. -/
structure StrictShortExact (S : ShortComplex C) : Prop where
  shortExact : S.ShortExact
  strict_f : IsStrict S.f
  strict_g : IsStrict S.g

end

section

variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasKernels D] [HasCokernels D]

/-- The canonical kernel sequence of a strict epimorphism is strict short
exact. -/
@[nolint unusedArguments]
theorem IsStrictEpi.strictShortExact_kernel {X Y : D} (q : X ⟶ Y)
    [HasZeroObject D] (hq : IsStrictEpi q) :
    StrictShortExact
      (ShortComplex.mk (kernel.ι q) q (kernel.condition q)) := by
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  change StrictShortExact S
  letI : Epi q := hq.epi
  have hExact : S.Exact := by
    let hLeft : S.LeftHomologyData :=
      ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
    let hRight : S.RightHomologyData :=
      ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
    have hlift : kernel.lift q (kernel.ι q) (kernel.condition q) = 𝟙 _ := by
      apply (cancel_mono (kernel.ι q)).1
      rw [kernel.lift_ι, Category.id_comp]
    have hLeftZero : IsZero hLeft.H := by
      haveI : Epi (kernel.lift q (kernel.ι q) (kernel.condition q)) := by
        rw [hlift]
        infer_instance
      dsimp [hLeft]
      exact isZero_cokernel_of_epi _
    have hdesc : cokernel.desc (kernel.ι q) q (kernel.condition q) =
        Abelian.coimageImageComparison q ≫ kernel.ι (cokernel.π q) := by
      apply (cancel_epi (cokernel.π (kernel.ι q))).1
      rw [cokernel.π_desc]
      symm
      exact Abelian.coimage_image_factorisation (f := q)
    have hRightZero : IsZero hRight.H := by
      letI : IsIso (Abelian.coimageImageComparison q) := hq.strict
      letI : IsIso (kernel.ι (cokernel.π q)) :=
        kernel.of_cokernel_of_epi (f := q)
      haveI : Mono (cokernel.desc (kernel.ι q) q (kernel.condition q)) := by
        rw [hdesc]
        infer_instance
      dsimp [hRight]
      exact isZero_kernel_of_mono _
    have hComp : hLeft.i ≫ hRight.p = 0 := by
      dsimp [hLeft, hRight]
      exact cokernel.condition (kernel.ι q)
    let hData : S.HomologyData :=
      { left := hLeft
        right := hRight
        iso := IsZero.iso hLeftZero hRightZero
        comm := by
          have hπZero : hLeft.π = 0 := hLeftZero.eq_of_tgt _ _
          simpa [hπZero, Category.assoc] using hComp.symm }
    exact ⟨⟨hData, hLeftZero⟩⟩
  refine ⟨ShortComplex.ShortExact.mk' hExact inferInstance inferInstance,
    ?_, hq.strict⟩
  exact (isStrictMono_kernel q).strict

end

section

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- Every morphism in an abelian category is strict. -/
theorem isStrict_of_abelian {X Y : D} (f : X ⟶ Y) : IsStrict f :=
  show IsIso _ from inferInstance

/-- Every monomorphism in an abelian category is strict. -/
theorem isStrictMono_of_mono {X Y : D} (f : X ⟶ Y) [Mono f] :
    IsStrictMono f :=
  ⟨inferInstance, isStrict_of_abelian f⟩

/-- Every epimorphism in an abelian category is strict. -/
theorem isStrictEpi_of_epi {X Y : D} (f : X ⟶ Y) [Epi f] :
    IsStrictEpi f :=
  ⟨inferInstance, isStrict_of_abelian f⟩

/-- Every short exact sequence in an abelian category is strictly short
exact. -/
theorem strictShortExact_of_shortExact {S : ShortComplex D}
    (h : S.ShortExact) : StrictShortExact S :=
  ⟨h, isStrict_of_abelian S.f, isStrict_of_abelian S.g⟩

end


section

variable [HasKernels C] [HasCokernels C]

variable {X : C}

/-- A strict subobject is one whose canonical inclusion is an owner strict
monomorphism. -/
def IsStrictSubobject (P : Subobject X) : Prop :=
  IsStrictMono P.arrow

@[simp]
theorem isStrictSubobject_iff (P : Subobject X) :
    IsStrictSubobject P ↔ IsStrictMono P.arrow :=
  Iff.rfl

/-- The ordered type of strict subobjects of an object. -/
abbrev StrictSubobject (X : C) :=
  {P : Subobject X // IsStrictSubobject P}

/-- Objects satisfying the descending chain condition on strict subobjects. -/
def isStrictArtinianObject : ObjectProperty C :=
  fun X ↦ WellFoundedLT (StrictSubobject X)

/-- Proposition-level strict-Artinian predicate. -/
abbrev IsStrictArtinianObject (X : C) : Prop :=
  isStrictArtinianObject.Is X

instance {X : C} [IsStrictArtinianObject X] :
    WellFoundedLT (StrictSubobject X) :=
  isStrictArtinianObject.prop_of_is X

/-- Objects satisfying the ascending chain condition on strict subobjects. -/
def isStrictNoetherianObject : ObjectProperty C :=
  fun X ↦ WellFoundedGT (StrictSubobject X)

/-- Proposition-level strict-Noetherian predicate. -/
abbrev IsStrictNoetherianObject (X : C) : Prop :=
  isStrictNoetherianObject.Is X

instance {X : C} [IsStrictNoetherianObject X] :
    WellFoundedGT (StrictSubobject X) :=
  isStrictNoetherianObject.prop_of_is X

/-- An Artinian object is strict-Artinian. -/
theorem isStrictArtinianObject_of_isArtinianObject {X : C}
    [IsArtinianObject X] : IsStrictArtinianObject X := by
  let f : StrictSubobject X → Subobject X := Subtype.val
  exact ObjectProperty.is_of_prop _
    ⟨InvImage.wf f
      (wellFounded_lt : WellFounded ((· < ·) : Subobject X → Subobject X → Prop))⟩

/-- A Noetherian object is strict-Noetherian. -/
theorem isStrictNoetherianObject_of_isNoetherianObject {X : C}
    [IsNoetherianObject X] : IsStrictNoetherianObject X := by
  let f : StrictSubobject X → Subobject X := Subtype.val
  exact ObjectProperty.is_of_prop _
    ⟨InvImage.wf f
      (wellFounded_gt : WellFounded ((· > ·) : Subobject X → Subobject X → Prop))⟩

end


section

variable {D : Type u} [Category.{v} D] [Abelian D]

variable {X : D}

/-- A strict-Artinian object in an abelian category is Artinian. -/
theorem isArtinianObject_of_isStrictArtinianObject [IsStrictArtinianObject X] :
    IsArtinianObject X := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  let g : ℕ →o (StrictSubobject X)ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual ⟨f n, by
        exact (isStrictSubobject_iff _).2
          (isStrictMono_of_mono (Subobject.arrow (f n)))⟩,
      fun i j hij ↦ f.2 hij⟩
  haveI : WellFoundedGT (StrictSubobject X)ᵒᵈ := by
    rw [wellFoundedGT_dual_iff]
    infer_instance
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
  exact ⟨n, fun m hm ↦ by
    have h := congrArg
      (fun S : (StrictSubobject X)ᵒᵈ => OrderDual.toDual S.ofDual.1) (hn m hm)
    change OrderDual.toDual (f n) = OrderDual.toDual (f m) at h
    exact h⟩

/-- A strict-Noetherian object in an abelian category is Noetherian. -/
theorem isNoetherianObject_of_isStrictNoetherianObject
    [IsStrictNoetherianObject X] : IsNoetherianObject X := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let g : ℕ →o StrictSubobject X :=
    ⟨fun n ↦ ⟨f n, by
        exact (isStrictSubobject_iff _).2
          (isStrictMono_of_mono (Subobject.arrow (f n)))⟩,
      fun i j hij ↦ f.2 hij⟩
  obtain ⟨n, hn⟩ := WellFoundedGT.monotone_chain_condition g
  exact ⟨n, fun m hm ↦ by
    have h := congrArg (fun S : StrictSubobject X => S.1) (hn m hm)
    change f n = f m at h
    exact h⟩

end


section

variable {A : Type u} [Category.{v} A]
  {D : Type u} [Category.{v} D]

/-- The map on subobjects induced by a full faithful functor preserving
monomorphisms. -/
@[nolint unusedArguments]
noncomputable def subobjectImageOfFullFaithful (F : A ⥤ D)
    [F.Full] [F.Faithful] [F.PreservesMonomorphisms] {E : A} :
    Subobject E → Subobject (F.obj E) :=
  Subobject.lift (fun {S} (f : S ⟶ E) [Mono f] ↦ Subobject.mk (F.map f))
    (fun {S₁ S₂} f g [Mono f] [Mono g] i w ↦
      Subobject.mk_eq_mk_of_comm _ _ (F.mapIso i) (by
        change F.map i.hom ≫ F.map g = F.map f
        rw [← F.map_comp, w]))

/-- The induced map on subobjects is injective. -/
theorem subobjectImageOfFullFaithful_injective (F : A ⥤ D)
    [F.Full] [F.Faithful] [F.PreservesMonomorphisms] {E : A} :
    Function.Injective
      (subobjectImageOfFullFaithful (A := A) (D := D) F (E := E)) := by
  intro s₁ s₂ heq
  induction s₁ using Subobject.ind
  induction s₂ using Subobject.ind
  rename_i S₁ f₁ _ S₂ f₂ _
  change Subobject.mk (F.map f₁) = Subobject.mk (F.map f₂) at heq
  exact Subobject.mk_eq_mk_of_comm f₁ f₂
    (F.preimageIso (Subobject.isoOfMkEqMk _ _ heq))
    (F.map_injective (by
      simp only [Functor.preimageIso_hom, Functor.map_comp,
        Functor.map_preimage]
      exact Subobject.ofMkLEMk_comp heq.le))

/-- The induced map on subobjects is monotone. -/
theorem subobjectImageOfFullFaithful_monotone (F : A ⥤ D)
    [F.Full] [F.Faithful] [F.PreservesMonomorphisms] {E : A} :
    Monotone (subobjectImageOfFullFaithful (A := A) (D := D) F (E := E)) := by
  intro s₁ s₂ h
  induction s₁ using Subobject.ind
  induction s₂ using Subobject.ind
  rename_i S₁ f₁ _ S₂ f₂ _
  change Subobject.mk (F.map f₁) ≤ Subobject.mk (F.map f₂)
  exact Subobject.mk_le_mk_of_comm
    (F.map (Subobject.ofMkLEMk f₁ f₂ h)) (by
      rw [← F.map_comp]
      exact congrArg F.map (Subobject.ofMkLEMk_comp h))

/-- A full faithful functor preserving monomorphisms reflects finiteness of
subobject lattices. -/
theorem Finite.subobject_of_fullFaithful_preservesMono (F : A ⥤ D)
    [F.Full] [F.Faithful] [F.PreservesMonomorphisms] {E : A}
    (h : Finite (Subobject (F.obj E))) : Finite (Subobject E) :=
  Finite.of_injective
    (subobjectImageOfFullFaithful (A := A) (D := D) F)
    (subobjectImageOfFullFaithful_injective (A := A) (D := D) F)

/-- Artinian objects transfer across full faithful functors preserving
monomorphisms. -/
theorem isArtinianObject_of_fullFaithful_preservesMono (F : A ⥤ D)
    [F.Full] [F.Faithful] [F.PreservesMonomorphisms] {E : A}
    [IsArtinianObject (F.obj E)] : IsArtinianObject E := by
  rw [isArtinianObject_iff_antitone_chain_condition]
  intro f
  let g : ℕ →o (Subobject (F.obj E))ᵒᵈ :=
    ⟨fun n ↦ OrderDual.toDual <|
        subobjectImageOfFullFaithful (A := A) (D := D) F (E := E) (f n),
      fun i j hij ↦ by
        change subobjectImageOfFullFaithful (A := A) (D := D) F (f j) ≤
          subobjectImageOfFullFaithful (A := A) (D := D) F (f i)
        exact subobjectImageOfFullFaithful_monotone
          (A := A) (D := D) F (f.2 hij)⟩
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject g
  exact ⟨n, fun m hm ↦
    subobjectImageOfFullFaithful_injective (A := A) (D := D) F (by
      have h := congrArg
        (fun S : (Subobject (F.obj E))ᵒᵈ => OrderDual.ofDual S) (hn m hm)
      change subobjectImageOfFullFaithful (A := A) (D := D) F (f n) =
        subobjectImageOfFullFaithful (A := A) (D := D) F (f m) at h
      exact h)⟩

/-- Noetherian objects transfer across full faithful functors preserving
monomorphisms. -/
theorem isNoetherianObject_of_fullFaithful_preservesMono (F : A ⥤ D)
    [F.Full] [F.Faithful] [F.PreservesMonomorphisms] {E : A}
    [IsNoetherianObject (F.obj E)] : IsNoetherianObject E := by
  rw [isNoetherianObject_iff_monotone_chain_condition]
  intro f
  let g : ℕ →o Subobject (F.obj E) :=
    ⟨fun n ↦ subobjectImageOfFullFaithful
        (A := A) (D := D) F (E := E) (f n),
      fun i j hij ↦ subobjectImageOfFullFaithful_monotone
        (A := A) (D := D) F (f.2 hij)⟩
  obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject g
  exact ⟨n, fun m hm ↦
    subobjectImageOfFullFaithful_injective (A := A) (D := D) F (hn m hm)⟩

end


section

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
  [HasKernels A] [HasCokernels A]
  {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
  [HasKernels D] [HasCokernels D]

/-- A full faithful functor that maps strict monomorphisms induces a map from
owner strict subobjects to ambient subobjects. -/
@[nolint unusedArguments]
noncomputable def strictSubobjectImageOfFullFaithful (F : A ⥤ D)
    [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y),
      IsStrictMono f → IsStrictMono (F.map f)) {E : A} :
    StrictSubobject E → Subobject (F.obj E) :=
  fun B ↦ by
    let hstrict : IsStrictMono (F.map B.1.arrow) := hF B.1.arrow B.2
    letI : Mono (F.map B.1.arrow) := hstrict.mono
    exact Subobject.mk (F.map B.1.arrow)

/-- The ambient-subobject image of owner strict subobjects is monotone. -/
theorem strictSubobjectImageOfFullFaithful_monotone (F : A ⥤ D)
    [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y),
      IsStrictMono f → IsStrictMono (F.map f)) {E : A} :
    Monotone
      (strictSubobjectImageOfFullFaithful (A := A) (D := D) F hF
        (E := E)) := by
  intro B₁ B₂ hB
  let hstrict₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  let hstrict₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hstrict₁.mono
  letI : Mono (F.map B₂.1.arrow) := hstrict₂.mono
  have hB' : B₁.1 ≤ B₂.1 := by simpa using hB
  have hmk : Subobject.mk B₁.1.arrow ≤ Subobject.mk B₂.1.arrow := by
    simpa [Subobject.mk_arrow] using hB'
  change Subobject.mk (F.map B₁.1.arrow) ≤
    Subobject.mk (F.map B₂.1.arrow)
  exact Subobject.mk_le_mk_of_comm
    (F.map (Subobject.ofMkLEMk B₁.1.arrow B₂.1.arrow hmk)) (by
      rw [← F.map_comp]
      exact congrArg F.map (Subobject.ofMkLEMk_comp hmk))

/-- The ambient-subobject image of owner strict subobjects is injective. -/
theorem strictSubobjectImageOfFullFaithful_injective (F : A ⥤ D)
    [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y),
      IsStrictMono f → IsStrictMono (F.map f)) {E : A} :
    Function.Injective
      (strictSubobjectImageOfFullFaithful (A := A) (D := D) F hF
        (E := E)) := by
  intro B₁ B₂ hEq
  let hstrict₁ : IsStrictMono (F.map B₁.1.arrow) := hF B₁.1.arrow B₁.2
  let hstrict₂ : IsStrictMono (F.map B₂.1.arrow) := hF B₂.1.arrow B₂.2
  letI : Mono (F.map B₁.1.arrow) := hstrict₁.mono
  letI : Mono (F.map B₂.1.arrow) := hstrict₂.mono
  apply Subtype.ext
  have hEq' : Subobject.mk (F.map B₁.1.arrow) =
      Subobject.mk (F.map B₂.1.arrow) := hEq
  simpa [Subobject.mk_arrow] using
    (Subobject.mk_eq_mk_of_comm B₁.1.arrow B₂.1.arrow
      (F.preimageIso (Subobject.isoOfMkEqMk _ _ hEq'))
      (F.map_injective (by
        simp only [Functor.preimageIso_hom, Functor.map_comp,
          Functor.map_preimage]
        exact Subobject.ofMkLEMk_comp hEq'.le)))

/-- Strict-Artinian objects transfer across full faithful functors that map
strict monomorphisms to strict monomorphisms. -/
theorem isStrictArtinianObject_of_fullFaithful_map_strictMono (F : A ⥤ D)
    [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y),
      IsStrictMono f → IsStrictMono (F.map f)) {E : A}
    [IsArtinianObject (F.obj E)] : IsStrictArtinianObject E :=
  ObjectProperty.is_of_prop _
    (show WellFoundedLT (StrictSubobject E) from by
      rw [← wellFoundedGT_dual_iff,
        wellFoundedGT_iff_monotone_chain_condition]
      intro f
      let g : ℕ →o (Subobject (F.obj E))ᵒᵈ :=
        ⟨fun n ↦ OrderDual.toDual <|
            strictSubobjectImageOfFullFaithful
              (A := A) (D := D) F hF (E := E) (f n),
          fun i j hij ↦ by
            change strictSubobjectImageOfFullFaithful
                (A := A) (D := D) F hF (f j) ≤
              strictSubobjectImageOfFullFaithful
                (A := A) (D := D) F hF (f i)
            exact strictSubobjectImageOfFullFaithful_monotone
              (A := A) (D := D) F hF (f.2 hij)⟩
      obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject g
      exact ⟨n, fun m hm ↦
        strictSubobjectImageOfFullFaithful_injective
          (A := A) (D := D) F hF (by
            have h := congrArg
              (fun S : (Subobject (F.obj E))ᵒᵈ => OrderDual.ofDual S)
              (hn m hm)
            change strictSubobjectImageOfFullFaithful
                (A := A) (D := D) F hF (f n) =
              strictSubobjectImageOfFullFaithful
                (A := A) (D := D) F hF (f m) at h
            exact h)⟩)

/-- Strict-Noetherian objects transfer across full faithful functors that map
strict monomorphisms to strict monomorphisms. -/
theorem isStrictNoetherianObject_of_fullFaithful_map_strictMono
    (F : A ⥤ D) [F.Full] [F.Faithful]
    (hF : ∀ {X Y : A} (f : X ⟶ Y),
      IsStrictMono f → IsStrictMono (F.map f)) {E : A}
    [IsNoetherianObject (F.obj E)] : IsStrictNoetherianObject E :=
  ObjectProperty.is_of_prop _
    (show WellFoundedGT (StrictSubobject E) from by
      rw [wellFoundedGT_iff_monotone_chain_condition]
      intro f
      let g : ℕ →o Subobject (F.obj E) :=
        ⟨fun n ↦ strictSubobjectImageOfFullFaithful
            (A := A) (D := D) F hF (E := E) (f n),
          fun i j hij ↦
            strictSubobjectImageOfFullFaithful_monotone
              (A := A) (D := D) F hF (f.2 hij)⟩
      obtain ⟨n, hn⟩ := monotone_chain_condition_of_isNoetherianObject g
      exact ⟨n, fun m hm ↦
        strictSubobjectImageOfFullFaithful_injective
          (A := A) (D := D) F hF (hn m hm)⟩)

end


section

variable [HasKernels C] [HasCokernels C]

/-- Both chain conditions on `StrictSubobject X` at once.

The conditions are stated on strict subobjects rather than on all of
`Subobject X` because that is the order a quasi-abelian category actually
controls: a strict monomorphism is exactly one that is the kernel of its own
cokernel (`IsStrictMono.isLimitKernelFork`), so a strict subobject has a
well-behaved quotient and a non-strict one need not. This is the hypothesis
Harder–Narasimhan recursion needs — it terminates
on chains of strict subobjects — and it is strictly weaker than
`IsFiniteLengthObject` in general, because `StrictSubobject X` is a subtype of
`Subobject X` and a chain condition on a subtype is the easier statement. The
two coincide exactly when every mono is strict, which
`isStrictFiniteLengthObject_iff_isFiniteLengthObject` records for abelian
categories. -/
def IsStrictFiniteLengthObject (X : C) : Prop :=
  IsStrictArtinianObject X ∧ IsStrictNoetherianObject X

/-- Both chain conditions on `Subobject X` at once.

Mathlib has `IsArtinianObject` and `IsNoetherianObject` but no bundled
object-level finite-length predicate, so this is defined here rather than
imported; it is a plausible upstreaming candidate. It exists in this file only
to state the comparison results below — the owner API is built on
`IsStrictFiniteLengthObject`. -/
def IsFiniteLengthObject (X : C) : Prop :=
  IsArtinianObject X ∧ IsNoetherianObject X

/-- Destructure strict finite length into its two chain conditions.

Definitionally `Iff.rfl`. It exists so that a deformation hypothesis carrying
an `IsStrictFiniteLengthObject` can produce the two instances without callers
unfolding the definition, which keeps later proofs stable if the conjunction is
ever replaced by a structure. -/
theorem isStrictFiniteLengthObject_iff {X : C} :
    IsStrictFiniteLengthObject X ↔
      IsStrictArtinianObject X ∧ IsStrictNoetherianObject X :=
  Iff.rfl

/-- The descending chain condition carried by strict finite length.

A deformation hypothesis arrives as a bare `IsStrictFiniteLengthObject X`, but
every consumer downstream wants the chain conditions as instances, so the
recurring idiom is `letI := h.isStrictArtinianObject`. Going through the named
projection rather than `h.1` keeps those call sites readable and unbroken if
the conjunction ever becomes a structure. -/
theorem IsStrictFiniteLengthObject.isStrictArtinianObject {X : C}
    (h : IsStrictFiniteLengthObject X) : IsStrictArtinianObject X :=
  h.1

/-- The ascending chain condition carried by strict finite length.

See `IsStrictFiniteLengthObject.isStrictArtinianObject` for why this is a named
projection rather than `h.2`. -/
theorem IsStrictFiniteLengthObject.isStrictNoetherianObject {X : C}
    (h : IsStrictFiniteLengthObject X) : IsStrictNoetherianObject X :=
  h.2

/-- Assemble strict finite length from the two chain conditions as instances.

The mirror image of the projections: consumers hand back instances, and this is
what turns them into the packaged hypothesis without an anonymous constructor
at every call site. -/
theorem IsStrictFiniteLengthObject.mk' {X : C} [IsStrictArtinianObject X]
    [IsStrictNoetherianObject X] : IsStrictFiniteLengthObject X :=
  ⟨inferInstance, inferInstance⟩

-- The ordinary chain conditions are stated on `Subobject X`, which needs no
-- kernels or cokernels; only the strict ones above do.
omit [HasZeroMorphisms C] [HasKernels C] [HasCokernels C] in
/-- The descending chain condition carried by ordinary finite length. -/
theorem IsFiniteLengthObject.isArtinianObject {X : C}
    (h : IsFiniteLengthObject X) : IsArtinianObject X :=
  h.1

omit [HasZeroMorphisms C] [HasKernels C] [HasCokernels C] in
/-- The ascending chain condition carried by ordinary finite length. -/
theorem IsFiniteLengthObject.isNoetherianObject {X : C}
    (h : IsFiniteLengthObject X) : IsNoetherianObject X :=
  h.2

omit [HasZeroMorphisms C] [HasKernels C] [HasCokernels C] in
/-- Assemble ordinary finite length from the two chain conditions as
instances. -/
theorem IsFiniteLengthObject.mk' {X : C} [IsArtinianObject X]
    [IsNoetherianObject X] : IsFiniteLengthObject X :=
  ⟨inferInstance, inferInstance⟩

/-- Finitely many subobjects force strict finite length.

Both halves come from the single `Finite (Subobject X)` hypothesis: it makes
the subtype `StrictSubobject X` finite, and a finite order is well-founded in
both directions at once, so neither chain condition needs a separate argument.
This is the constructor to reach for on an object of a heart with finitely many
subobjects, where checking the chain conditions directly would mean an
induction. -/
theorem isStrictFiniteLengthObject_of_finite_subobjects {X : C}
    (h : Finite (Subobject X)) : IsStrictFiniteLengthObject X := by
  letI : Finite (Subobject X) := h
  exact ⟨ObjectProperty.is_of_prop _
      (show WellFoundedLT (StrictSubobject X) from by infer_instance),
    ObjectProperty.is_of_prop _
      (show WellFoundedGT (StrictSubobject X) from by infer_instance)⟩

/-- Finite length implies strict finite length, in any quasi-abelian category.

The implication runs this way and not the other because well-foundedness
restricts along the inclusion `StrictSubobject X ↪ Subobject X`: a chain of
strict subobjects is in particular a chain of subobjects, so both conditions
transport by `InvImage.wf`. Recovering the converse needs every mono to be
strict, and so is available only under `Abelian` — see
`isStrictFiniteLengthObject_iff_isFiniteLengthObject`. -/
theorem isStrictFiniteLengthObject_of_isFiniteLengthObject {X : C}
    (h : IsFiniteLengthObject X) : IsStrictFiniteLengthObject X := by
  letI : IsArtinianObject X := h.isArtinianObject
  letI : IsNoetherianObject X := h.isNoetherianObject
  exact ⟨isStrictArtinianObject_of_isArtinianObject,
    isStrictNoetherianObject_of_isNoetherianObject⟩

end


section

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- Over an abelian category the strict and ordinary notions agree.

`Abelian` is what collapses the distinction: every monomorphism is strict, so
`StrictSubobject X` is the whole of `Subobject X` and the two chain conditions
are the same statement. Only the forward direction consumes the hypothesis; the
reverse is the general implication above. The practical use is to import
finite-length facts about a heart, which is abelian, into the quasi-abelian
interval categories where the owner theory lives — the transfer is sound in
that direction precisely because this equivalence is unavailable in the
quasi-abelian setting itself. -/
theorem isStrictFiniteLengthObject_iff_isFiniteLengthObject {X : D} :
    IsStrictFiniteLengthObject X ↔ IsFiniteLengthObject X := by
  constructor
  · intro h
    letI : IsStrictArtinianObject X := h.isStrictArtinianObject
    letI : IsStrictNoetherianObject X := h.isStrictNoetherianObject
    exact ⟨isArtinianObject_of_isStrictArtinianObject,
      isNoetherianObject_of_isStrictNoetherianObject⟩
  · exact isStrictFiniteLengthObject_of_isFiniteLengthObject

end


end CategoryTheory.Triangulated
