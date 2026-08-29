/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.QuasiAbelian
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Slicing.IntervalComparisons
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Strict morphisms detected by adjacent slicing hearts

For a thin slicing interval, monicity in the right adjacent heart detects a
strict monomorphism, while epicity in the left adjacent heart detects a strict
epimorphism.  The proof transports the abelian kernel/cokernel universal
property across the owner comparison isomorphisms and reflects it through the
fully faithful interval embedding.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.TStructure
open CategoryTheory.Triangulated.TStructure

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

section

variable {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- Open slicing intervals are invariant under isomorphism. -/
instance Slicing.intervalProp_isClosedUnderIsomorphisms (s : Slicing C) :
    (s.intervalProp C a b).IsClosedUnderIsomorphisms where
  of_iso e h := h.elim
    (fun hE ↦ Or.inl (IsZero.of_iso hE e.symm))
    (fun ⟨F, hF⟩ ↦ Or.inr ⟨F.ofIso C e, hF⟩)

/-- A strict monomorphism in a thin interval becomes monic in the right
adjacent heart. -/
theorem Slicing.IntervalCat.mono_toRightHeart_of_strictMono (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let q : Y ⟶ cokernel f := cokernel.π f
  let qH : FR.obj Y ⟶ FR.obj (cokernel f) := FR.map q
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso
    (C := C) (s := s) (a := a) (b := b) f
  have hqHeq : qH ≫ eQ.hom = cokernel.π (FR.map f) := by
    simpa [qH, FR, eQ] using
      Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
        (C := C) (s := s) (a := a) (b := b) f
  have himage_zero : Abelian.image.ι (FR.map f) ≫ qH = 0 := by
    apply (cancel_mono eQ.hom).1
    rw [Category.assoc, hqHeq, zero_comp]
    change kernel.ι (cokernel.π (FR.map f)) ≫ cokernel.π (FR.map f) = 0
    exact kernel.condition (cokernel.π (FR.map f))
  have himage_kernel : IsLimit
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero) :=
    isKernelOfComp (f := qH) eQ.hom (cokernel.π (FR.map f))
      (kernelIsKernel (cokernel.π (FR.map f))) himage_zero hqHeq
  have hkernel_qH :
      IsLimit (KernelFork.ofι (kernel.ι qH) (kernel.condition qH)) := by
    simpa using kernelIsKernel qH
  let eKh : Abelian.image (FR.map f) ⟶ kernel qH :=
    hkernel_qH.lift
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
  have heKh : eKh ≫ kernel.ι qH = Abelian.image.ι (FR.map f) := by
    dsimp only [eKh]
    exact hkernel_qH.fac
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
      Limits.WalkingParallelPair.zero
  let eKi : kernel qH ⟶ Abelian.image (FR.map f) :=
    himage_kernel.lift
      (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
  have heKi : eKi ≫ Abelian.image.ι (FR.map f) = kernel.ι qH := by
    dsimp only [eKi]
    exact himage_kernel.fac
      (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
      Limits.WalkingParallelPair.zero
  let eK : Abelian.image (FR.map f) ≅ kernel qH := by
    refine ⟨eKh, eKi, ?_, ?_⟩
    · apply (cancel_mono (Abelian.image.ι (FR.map f))).1
      rw [Category.assoc, heKi, heKh]
      simp
    · apply (cancel_mono (kernel.ι qH)).1
      rw [Category.assoc, heKh, heKi]
      simp
  let iH : FR.obj X ⟶ kernel qH :=
    Abelian.factorThruImage (FR.map f) ≫ eK.hom
  have hiH : iH ≫ kernel.ι qH = FR.map f := by
    change (Abelian.factorThruImage (FR.map f) ≫ eK.hom) ≫
      kernel.ι qH = FR.map f
    rw [Category.assoc, heKh, Abelian.image.fac]
  haveI : Epi iH := by
    letI : IsIso eK.hom := ⟨⟨eK.inv, eK.hom_inv_id, eK.inv_hom_id⟩⟩
    exact CategoryTheory.epi_comp'
      (CategoryTheory.Abelian.instEpiFactorThruImage (f := FR.map f))
      inferInstance
  have hK_mem : s.intervalProp C a b (kernel qH).obj :=
    s.intervalProp_of_epi_rightHeart (C := C) (a := a) (b := b)
      (Fact.out : a < b) X.property iH
  let KI : s.IntervalCat C a b := ⟨(kernel qH).obj, hK_mem⟩
  let k : KI ⟶ Y := ObjectProperty.homMk (kernel.ι qH).hom
  let i : X ⟶ KI := ObjectProperty.homMk iH.hom
  have hk_zero : k ≫ q = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι qH ≫ qH).hom = 0
    simp
  have hi : i ≫ k = f := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (iH ≫ kernel.ι qH).hom = (FR.map f).hom
    rw [hiH]
  have hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W} g hg ↦ ?_)
      (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
    · let gH := FR.map g
      have hgH : gH ≫ qH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ q.hom = 0
        exact congr_arg (·.hom) hg
      exact ObjectProperty.homMk (kernel.lift qH gH hgH).hom
    · let gH := FR.map g
      have hgH : gH ≫ qH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ q.hom = 0
        exact congr_arg (·.hom) hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift qH gH hgH ≫ kernel.ι qH).hom = g.hom
      simp [gH, FR]
    · let gH := FR.map g
      have hgH : gH ≫ qH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ q.hom = 0
        exact congr_arg (·.hom) hg
      let mH : FR.obj W ⟶ kernel qH := ObjectProperty.homMk m.hom
      have hmH : mH ≫ kernel.ι qH = kernel.lift qH gH hgH ≫ kernel.ι qH := by
        apply t.ιHeart.map_injective
        change m.hom ≫ (kernel.ι qH).hom =
          (kernel.lift qH gH hgH ≫ kernel.ι qH).hom
        simp [gH, FR]
        exact congr_arg (·.hom) hm
      have hmEq : mH = kernel.lift qH gH hgH :=
        Fork.IsLimit.hom_ext (kernelIsKernel qH) hmH
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift qH gH hgH).hom
      simpa [mH] using congr_arg (·.hom) hmEq
  let e : X ≅ KI :=
    IsLimit.conePointUniqueUpToIso hf.isLimitKernelFork hk_limit
  have he : e.hom ≫ k = f := by
    dsimp only [e]
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      hf.isLimitKernelFork hk_limit Limits.WalkingParallelPair.zero
  let j : kernel qH ≅ FR.obj KI := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have hk_map : j.inv ≫ kernel.ι qH = FR.map k := by
    apply t.ιHeart.map_injective
    change (j.inv ≫ kernel.ι qH).hom = (FR.map k).hom
    simp [FR, k, j]
  have hk_eq : FR.map k = j.inv ≫ kernel.ι qH := hk_map.symm
  let eH : FR.obj X ≅ FR.obj KI := FR.mapIso e
  have hmapf : eH.hom ≫ FR.map k = FR.map f := by
    simpa [eH] using congrArg FR.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
  haveI : Mono (eH.hom ≫ (j.inv ≫ kernel.ι qH)) := inferInstance
  have hfac : FR.map f ≫ 𝟙 _ = eH.hom ≫ (j.inv ≫ kernel.ι qH) := by
    simpa [Category.comp_id, hk_eq, Category.assoc] using hmapf.symm
  exact mono_of_mono_fac hfac

/-- A map in a thin interval which becomes monic in the right adjacent heart
is a strict monomorphism. -/
theorem Slicing.IntervalCat.strictMono_of_mono_toRightHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y)
    [Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f)] :
    IsStrictMono f := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso
    (C := C) (s := s) (a := a) (b := b) f
  let eDiag :
      parallelPair (FR.map (cokernel.π f)) 0 ≅
        parallelPair (cokernel.π (FR.map f)) 0 :=
    parallelPair.ext (Iso.refl _) eQ
      (by
        simpa [FR, eQ] using
          Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
            (C := C) (s := s) (a := a) (b := b) f)
      (by simp)
  have hlim' : IsLimit
      (KernelFork.ofι (FR.map f) (by
        apply t.ιHeart.map_injective
        change (f ≫ cokernel.π f).hom = 0
        simp) : Fork (FR.map (cokernel.π f)) 0) := by
    let c : Fork (cokernel.π (FR.map f)) 0 :=
      KernelFork.ofι (FR.map f) (cokernel.condition (FR.map f))
    let q : Cofork (FR.map f) 0 :=
      CokernelCofork.ofπ (cokernel.π (FR.map f))
        (cokernel.condition (FR.map f))
    have hcanon : IsLimit c :=
      Abelian.monoIsKernelOfCokernel q (cokernelIsCokernel (FR.map f))
    let htrans := (IsLimit.postcomposeInvEquiv eDiag c).symm hcanon
    exact IsLimit.ofIsoLimit htrans <|
      Fork.ext (Iso.refl _) (by
        change (Iso.refl _).hom ≫ c.ι =
          c.ι ≫ eDiag.inv.app WalkingParallelPair.zero
        simp [eDiag])
  have hmap : IsLimit
      (FR.mapCone (KernelFork.ofι f (cokernel.condition f))) :=
    (isLimitMapConeForkEquiv' FR (cokernel.condition f)).symm hlim'
  have hlim : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    isLimitOfReflects FR hmap
  exact isStrictMono_of_isLimitKernelFork hlim

/-- A strict epimorphism in a thin interval becomes epic in the left adjacent
heart. -/
theorem Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictEpi f) :
    Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let k : kernel f ⟶ X := kernel.ι f
  let kH : FL.obj (kernel f) ⟶ FL.obj X := FL.map k
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso
    (C := C) (s := s) (a := a) (b := b) f
  let eQ : cokernel kH ≅ cokernel (kernel.ι (FL.map f)) :=
    cokernel.mapIso kH (kernel.ι (FL.map f)) eK (Iso.refl _)
      (by
        simpa [kH, FL] using
          (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
            (C := C) (s := s) (a := a) (b := b) f).symm)
  let d : cokernel kH ⟶ FL.obj Y :=
    eQ.hom ≫ Abelian.factorThruCoimage (FL.map f)
  have hd : cokernel.π kH ≫ d = FL.map f := by
    calc
      cokernel.π kH ≫ d =
          cokernel.π kH ≫ eQ.hom ≫
            Abelian.factorThruCoimage (FL.map f) := by simp [d]
      _ = cokernel.π (kernel.ι (FL.map f)) ≫
            Abelian.factorThruCoimage (FL.map f) := by simp [eQ]
      _ = FL.map f := Abelian.coimage.fac (FL.map f)
  haveI : Mono d := by
    letI : CategoryTheory.NonPreadditiveAbelian t.heart.FullSubcategory :=
      CategoryTheory.Abelian.nonPreadditiveAbelian
        (C := t.heart.FullSubcategory)
    letI : IsIso eQ.hom := ⟨⟨eQ.inv, eQ.hom_inv_id, eQ.inv_hom_id⟩⟩
    letI : Mono eQ.hom := by infer_instance
    change Mono (eQ.hom ≫ Abelian.factorThruCoimage (FL.map f))
    exact CategoryTheory.mono_comp'
      (hg := inferInstance)
      (hf := CategoryTheory.Abelian.instMonoFactorThruCoimage (f := FL.map f))
  have hQ_mem : s.intervalProp C a b (cokernel kH).obj :=
    s.intervalProp_of_mono_leftHeart (C := C) (a := a) (b := b)
      (Fact.out : a < b) Y.property d
  let QI : s.IntervalCat C a b := ⟨(cokernel kH).obj, hQ_mem⟩
  let p : X ⟶ QI := ObjectProperty.homMk (cokernel.π kH).hom
  have hp_zero : k ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kH ≫ cokernel.π kH).hom = 0
    simp
  have hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W} g hg ↦ ?_)
      (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
    · let gH := FL.map g
      have hgH : kH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change k.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      exact ObjectProperty.homMk (cokernel.desc kH gH hgH).hom
    · let gH := FL.map g
      have hgH : kH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change k.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π kH ≫ cokernel.desc kH gH hgH).hom = g.hom
      simp [gH, FL]
    · let gH := FL.map g
      have hgH : kH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change k.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      let mH : cokernel kH ⟶ FL.obj W := ObjectProperty.homMk m.hom
      have hmH : cokernel.π kH ≫ mH =
          cokernel.π kH ≫ cokernel.desc kH gH hgH := by
        apply t.ιHeart.map_injective
        change (cokernel.π kH).hom ≫ m.hom =
          (cokernel.π kH ≫ cokernel.desc kH gH hgH).hom
        simp [gH, FL]
        simpa [mH, p] using congr_arg (·.hom) hm
      have hmEq : mH = cokernel.desc kH gH hgH :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel kH) hmH
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc kH gH hgH).hom
      simpa [mH] using congr_arg (·.hom) hmEq
  let e : QI ≅ Y :=
    IsColimit.coconePointUniqueUpToIso hp_colim hf.isColimitCokernelCofork
  have he : p ≫ e.hom = f := by
    dsimp only [e]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      hp_colim hf.isColimitCokernelCofork Limits.WalkingParallelPair.one
  let j : FL.obj QI ≅ cokernel kH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have hj : FL.map p ≫ j.hom = cokernel.π kH := by
    apply t.ιHeart.map_injective
    change (FL.map p ≫ j.hom).hom = (cokernel.π kH).hom
    simp [FL, p, j]
  have hp_eq : FL.map p = cokernel.π kH ≫ j.inv := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Mono j.hom := by infer_instance
    exact (cancel_mono j.hom).1 (by simpa [Category.assoc] using hj)
  have hp_epi : Epi (FL.map p) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Epi (cokernel.π kH ≫ j.inv) := inferInstance
    simpa [hp_eq]
  let eH : FL.obj QI ≅ FL.obj Y := FL.mapIso e
  have hmapf : FL.map p ≫ eH.hom = FL.map f := by
    simpa [eH] using congrArg FL.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Epi (FL.map p ≫ eH.hom) := inferInstance
  simpa [hmapf]

/-- A map in a thin interval which becomes epic in the left adjacent heart is
a strict epimorphism. -/
theorem Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y)
    [Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f)] :
    IsStrictEpi f := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso
    (C := C) (s := s) (a := a) (b := b) f
  let eDiag :
      parallelPair (FL.map (kernel.ι f)) 0 ≅
        parallelPair (kernel.ι (FL.map f)) 0 :=
    parallelPair.ext eK (Iso.refl _)
      (by
        simpa [FL, eK] using
          (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
            (C := C) (s := s) (a := a) (b := b) f).symm)
      (by simp)
  have hcolim' : IsColimit
      (CokernelCofork.ofπ (FL.map f) (by
        apply t.ιHeart.map_injective
        change (kernel.ι f ≫ f).hom = 0
        simp) : Cofork (FL.map (kernel.ι f)) 0) := by
    let c : Cofork (kernel.ι (FL.map f)) 0 :=
      CokernelCofork.ofπ (FL.map f) (kernel.condition (FL.map f))
    have hcanon : IsColimit c :=
      Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι (FL.map f))
          (kernel.condition (FL.map f)))
        (kernelIsKernel (FL.map f))
    let htrans := (IsColimit.precomposeHomEquiv eDiag c).symm hcanon
    exact IsColimit.ofIsoColimit htrans <|
      Cofork.ext (Iso.refl _) (by
        have hπ : Cofork.π ((Cocone.precompose eDiag.hom).obj c) =
            eDiag.hom.app WalkingParallelPair.one ≫ c.π := rfl
        have h₁ : Cofork.π ((Cocone.precompose eDiag.hom).obj c) ≫
              (Iso.refl ((Cocone.precompose eDiag.hom).obj c).pt).hom =
            eDiag.hom.app WalkingParallelPair.one ≫ c.π := by
          simpa [Category.assoc] using congrArg
            (fun k ↦ k ≫ (Iso.refl ((Cocone.precompose eDiag.hom).obj c).pt).hom) hπ
        have h₂ : eDiag.hom.app WalkingParallelPair.one ≫ c.π = FL.map f := by
          simp [c, eDiag]
        exact h₁.trans h₂)
  have hmap : IsColimit
      (FL.mapCocone (CokernelCofork.ofπ f (kernel.condition f))) :=
    (isColimitMapCoconeCoforkEquiv' FL (kernel.condition f)).symm hcolim'
  have hcolim : IsColimit (CokernelCofork.ofπ f (kernel.condition f)) :=
    isColimitOfReflects FL hmap
  exact isStrictEpi_of_isColimitCokernelCofork hcolim

/-- Strict epimorphisms in a thin interval are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictEpi (s : Slicing C)
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictEpi f) (hg : IsStrictEpi g) :
    IsStrictEpi (f ≫ g) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  haveI : Epi (FL.map f) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s f hf
  haveI : Epi (FL.map g) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s g hg
  haveI : Epi (FL.map (f ≫ g)) := by
    simpa using (show Epi (FL.map f ≫ FL.map g) by infer_instance)
  exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart C s (f ≫ g)

/-- If a composite is a strict epimorphism in a thin interval, then its
second factor is a strict epimorphism. -/
theorem Slicing.IntervalCat.strictEpi_of_comp_strictEpi (s : Slicing C)
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : IsStrictEpi (f ≫ g)) : IsStrictEpi g := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  haveI : Epi (FL.map (f ≫ g)) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s (f ≫ g) hfg
  have hfac : FL.map f ≫ FL.map g = FL.map (f ≫ g) := by simp
  haveI : Epi (FL.map g) := epi_of_epi_fac hfac
  exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart C s g

/-- Strict monomorphisms in a thin interval are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictMono (s : Slicing C)
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictMono f) (hg : IsStrictMono g) :
    IsStrictMono (f ≫ g) := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  haveI : Mono (FR.map f) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s f hf
  haveI : Mono (FR.map g) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s g hg
  haveI : Mono (FR.map (f ≫ g)) := by
    simpa using (show Mono (FR.map f ≫ FR.map g) by infer_instance)
  exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart C s (f ≫ g)

/-- The canonical arrow of an intrinsic admissible interval subobject is an
owner strict monomorphism. -/
theorem Slicing.IntervalCat.isStrictSubobject_of_isAdmissible
    (s : Slicing C) {E : s.IntervalCat C a b} (A : Subobject E)
    (hA : s.IsAdmissibleSubobject C A) : IsStrictSubobject A := by
  rcases hA with ⟨X, Q, i, hi, q, hAi, δ, hT⟩
  subst A
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have hshort :
      (ShortComplex.mk (FR.map i) (FR.map q) (by
        ext
        exact comp_distTriang_mor_zero₁₂ _ hT)).ShortExact :=
    heartFullSubcategory_shortExact_of_distTriang t hT
  letI : Mono (FR.map i) := hshort.mono_f
  have hiStrict : IsStrictMono i :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart C s i
  let e := Subobject.underlyingIso i
  have heStrict : IsStrictMono e.hom := isStrictMono_of_isIso
  have hcomp : IsStrictMono (e.hom ≫ i) :=
    Slicing.IntervalCat.comp_strictMono C s e.hom i heStrict hiStrict
  simpa [IsStrictSubobject, e] using hcomp

/-- Intrinsic admissible subobjects order-embed into owner strict
subobjects. -/
def Slicing.IntervalCat.admissibleToStrictSubobject (s : Slicing C)
    (E : s.IntervalCat C a b) :
    s.AdmissibleSubobject C E ↪o StrictSubobject E where
  toFun A := ⟨A.1,
    Slicing.IntervalCat.isStrictSubobject_of_isAdmissible C s A.1 A.2⟩
  inj' := by
    intro A B h
    have hval : A.1 = B.1 :=
      congrArg (fun Z : StrictSubobject E => Z.1) h
    exact Subtype.ext hval
  map_rel_iff' := Iff.rfl

/-- A strict-Artinian interval object is intrinsically admissibly
Artinian. -/
theorem Slicing.IntervalCat.isAdmissiblyArtinian_of_isStrictArtinian
    (s : Slicing C) {E : s.IntervalCat C a b}
    [IsStrictArtinianObject E] : s.IsAdmissiblyArtinian C E :=
  (Slicing.IntervalCat.admissibleToStrictSubobject C s E).strictMono.wellFoundedLT

/-- A strict-Noetherian interval object is intrinsically admissibly
Noetherian. -/
theorem Slicing.IntervalCat.isAdmissiblyNoetherian_of_isStrictNoetherian
    (s : Slicing C) {E : s.IntervalCat C a b}
    [IsStrictNoetherianObject E] : s.IsAdmissiblyNoetherian C E :=
  (Slicing.IntervalCat.admissibleToStrictSubobject C s E).strictMono.wellFoundedGT

/-- Owner strict finite length implies the intrinsic finite-length condition
used by owner local finiteness. -/
theorem Slicing.IntervalCat.isFiniteLength_of_isStrictFiniteLength
    (s : Slicing C) {E : s.IntervalCat C a b}
    (hE : IsStrictFiniteLengthObject E) : s.IsFiniteLength C E := by
  letI : IsStrictArtinianObject E := hE.1
  letI : IsStrictNoetherianObject E := hE.2
  exact ⟨Slicing.IntervalCat.isAdmissiblyArtinian_of_isStrictArtinian C s,
    Slicing.IntervalCat.isAdmissiblyNoetherian_of_isStrictNoetherian C s⟩

/-- A uniform strict finite-length bound on normalized thin intervals gives
owner local finiteness. -/
theorem Slicing.IsLocallyFinite.of_strictFiniteLength (s : Slicing C)
    {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2)
    (hfinite : ∀ t : ℝ,
      letI : Fact (t - η < t + η) := ⟨by linarith⟩
      letI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
      ∀ E : s.IntervalCat C (t - η) (t + η),
        IsStrictFiniteLengthObject E) : s.IsLocallyFinite C := by
  refine ⟨⟨η, hη, hη', fun t E ↦ ?_⟩⟩
  letI : Fact (t - η < t + η) := ⟨by linarith⟩
  letI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
  exact Slicing.IntervalCat.isFiniteLength_of_isStrictFiniteLength
    C s (hfinite t E)

/-- Uniform finiteness of subobject lattices on normalized thin intervals
gives owner local finiteness. -/
theorem Slicing.IsLocallyFinite.of_finiteSubobjects (s : Slicing C)
    {η : ℝ} (hη : 0 < η) (hη' : η < 1 / 2)
    (hfinite : ∀ t : ℝ,
      letI : Fact (t - η < t + η) := ⟨by linarith⟩
      letI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
      ∀ E : s.IntervalCat C (t - η) (t + η),
        Finite (Subobject E)) : s.IsLocallyFinite C := by
  apply Slicing.IsLocallyFinite.of_strictFiniteLength C s hη hη'
  intro t
  letI : Fact (t - η < t + η) := ⟨by linarith⟩
  letI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
  intro E
  exact isStrictFiniteLengthObject_of_finite_subobjects (hfinite t E)

/-- A distinguished ambient triangle on three thin-interval objects defines
an owner strict short exact sequence in the interval category. -/
theorem Slicing.IntervalCat.strictShortExact_of_distinguished
    (s : Slicing C) {S : ShortComplex (s.IntervalCat C a b)}
    {δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C) :
    StrictShortExact S := by
  let tL := (s.phaseShift C a).toTStructure C
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := heartFullSubcategoryAbelian tL
  let FL := Slicing.IntervalCat.toLeftHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have hL : (S.map FL).ShortExact := by
    change (ShortComplex.mk (FL.map S.f) (FL.map S.g) _).ShortExact
    exact heartFullSubcategory_shortExact_of_distTriang tL hT
  have hKerL : IsLimit
      (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := hL.fIsKernel
  have hKerMap : IsLimit
      (FL.mapCone (KernelFork.ofι S.f S.zero)) :=
    (isLimitMapConeForkEquiv' FL S.zero).symm hKerL
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitOfReflects FL hKerMap
  let tR := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := heartFullSubcategoryAbelian tR
  let FR := Slicing.IntervalCat.toRightHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  have hR : (S.map FR).ShortExact := by
    change (ShortComplex.mk (FR.map S.f) (FR.map S.g) _).ShortExact
    exact heartFullSubcategory_shortExact_of_distTriang tR hT
  have hCokR : IsColimit
      (CokernelCofork.ofπ ((S.map FR).g) (S.map FR).zero) := hR.gIsCokernel
  have hCokMap : IsColimit
      (FR.mapCocone (CokernelCofork.ofπ S.g S.zero)) :=
    (isColimitMapCoconeCoforkEquiv' FR S.zero).symm hCokR
  have hCok : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    isColimitOfReflects FR hCokMap
  letI : Mono (FR.map S.f) := hR.mono_f
  letI : Epi (FL.map S.g) := hL.epi_g
  have hf : IsStrictMono S.f :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart C s S.f
  have hg : IsStrictEpi S.g :=
    Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart C s S.g
  let eK' : kernel S.g ≅ S.X₁ :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hKer
  let eK : S.X₁ ≅ kernel S.g := eK'.symm
  have heK : eK.hom ≫ kernel.ι S.g = S.f := by
    change (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hKer).inv ≫
      kernel.ι S.g = S.f
    exact IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel S.g) hKer
      Limits.WalkingParallelPair.zero
  have hLift : kernel.lift S.g S.f S.zero = eK.hom := by
    apply (cancel_mono (kernel.ι S.g)).1
    rw [heK]
    exact kernel.lift_ι S.g S.f S.zero
  have hKernelComp : kernel.ι S.g ≫ cokernel.π S.f = 0 := by
    have hιEq : kernel.ι S.g = eK.inv ≫ S.f := by
      apply (cancel_epi eK.hom).1
      simp [heK]
    rw [hιEq, Category.assoc, cokernel.condition]
    simp
  let eQ : cokernel S.f ≅ S.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hCok
  have heQ : cokernel.π S.f ≫ eQ.hom = S.g := by
    change cokernel.π S.f ≫
        (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hCok).hom =
      (CokernelCofork.ofπ S.g S.zero).ι.app Limits.WalkingParallelPair.one
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel S.f) hCok Limits.WalkingParallelPair.one
  have hDesc : cokernel.desc S.f S.g S.zero = eQ.hom := by
    apply (cancel_epi (cokernel.π S.f)).1
    rw [heQ]
    exact cokernel.π_desc S.f S.g S.zero
  let hLeft : S.LeftHomologyData :=
    ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel S
  let hRight : S.RightHomologyData :=
    ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel S
  have hLeftZero : IsZero hLeft.H := by
    haveI : IsIso (kernel.lift S.g S.f S.zero) := by
      rw [hLift]
      infer_instance
    haveI : Epi (kernel.lift S.g S.f S.zero) := by infer_instance
    dsimp [hLeft]
    simpa [hLift] using isZero_cokernel_of_epi (kernel.lift S.g S.f S.zero)
  have hRightZero : IsZero hRight.H := by
    haveI : IsIso (cokernel.desc S.f S.g S.zero) := by
      rw [hDesc]
      infer_instance
    haveI : Mono (cokernel.desc S.f S.g S.zero) := by infer_instance
    dsimp [hRight]
    simpa [hDesc] using isZero_kernel_of_mono (cokernel.desc S.f S.g S.zero)
  have hComp : hLeft.i ≫ hRight.p = 0 := by
    dsimp [hLeft, hRight]
    exact hKernelComp
  have hExact : S.Exact := by
    let hData : S.HomologyData :=
      { left := hLeft
        right := hRight
        iso := IsZero.iso hLeftZero hRightZero
        comm := by
          have hπZero : hLeft.π = 0 := hLeftZero.eq_of_tgt _ _
          simpa [hπZero, Category.assoc] using hComp.symm }
    exact ⟨⟨hData, hLeftZero⟩⟩
  exact ⟨ShortComplex.ShortExact.mk' hExact hf.mono hg.epi,
    hf.strict, hg.strict⟩

omit [Fact (a < b)] in
set_option backward.isDefEq.respectTransparency false in
/-- A short exact sequence obtained in the left adjacent heart extends to an
ambient distinguished triangle with the original interval objects. -/
theorem Slicing.IntervalCat.exists_distinguished_of_shortExact_toLeftHeart
    (s : Slicing C) {S : ShortComplex (s.IntervalCat C a b)}
    (hL :
      (S.map (Slicing.IntervalCat.toLeftHeart
        (C := C) (s := s) a b (Fact.out : b - a ≤ 1))).ShortExact) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧),
      Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  letI : IsNormalMonoCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalMonoCategory
  letI : IsNormalEpiCategory t.heart.FullSubcategory :=
    Abelian.toIsNormalEpiCategory
  let FL := Slicing.IntervalCat.toLeftHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  letI : Balanced t.heart.FullSubcategory := by infer_instance
  letI : Epi ((S.map FL).g) := hL.epi_g
  obtain ⟨K, i, δ, hT⟩ :=
    exists_distinguished_triangle_of_heart_epi t ((S.map FL).g)
  have hKer : IsLimit
      (KernelFork.ofι i (show i ≫ (S.map FL).g = 0 by
        exact ι.map_injective (comp_distTriang_mor_zero₁₂ _ hT))) :=
    Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (heart_hι t) i ((S.map FL).g) δ hT
  have hLfIsKernel : IsLimit
      (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) := hL.fIsKernel
  let eK : K ≅ FL.obj S.X₁ :=
    IsLimit.conePointUniqueUpToIso hKer hLfIsKernel
  refine ⟨δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map eK.hom), ?_⟩
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (ι.mapIso eK.symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · simp only [Iso.refl_hom, Functor.mapIso_hom, Iso.symm_hom,
      Triangle.mk_mor₁]
    have hcomp : ι.map eK.inv ≫ ι.map i = S.f.hom := by
      have hmapf : ι.map ((S.map FL).f) = S.f.hom := rfl
      rw [← Functor.map_comp, ← hmapf]
      exact congrArg (fun k ↦ ι.map k)
        (IsLimit.conePointUniqueUpToIso_inv_comp hKer hLfIsKernel
          Limits.WalkingParallelPair.zero)
    change S.f.hom ≫ 𝟙 S.X₂.obj = ι.map eK.inv ≫ t.ιHeart.map i
    simpa [FL] using hcomp.symm
  · have hmap : t.ιHeart.map ((S.map FL).g) = S.g.hom := rfl
    simp only [Iso.refl_hom, Triangle.mk_mor₂]
    rw [hmap]
    simp
  · simp only [Iso.refl_hom, Triangle.mk_mor₃, Functor.mapIso_hom,
      Iso.symm_hom]
    change (δ ≫ (shiftFunctor C (1 : ℤ)).map (ι.map eK.hom)) ≫
        (shiftFunctor C (1 : ℤ)).map (ι.map eK.inv) = 𝟙 _ ≫ δ
    rw [Category.assoc, ← (shiftFunctor C (1 : ℤ)).map_comp,
      ← ι.map_comp, eK.hom_inv_id]
    have hιid : ι.map (𝟙 K) = 𝟙 (ι.obj K) := ι.map_id K
    rw [hιid]
    have hshift : (shiftFunctor C (1 : ℤ)).map (𝟙 (ι.obj K)) =
        𝟙 ((shiftFunctor C (1 : ℤ)).obj (ι.obj K)) :=
      (shiftFunctor C (1 : ℤ)).map_id (ι.obj K)
    rw [hshift, Category.comp_id, Category.id_comp]

/-- The left adjacent-heart embedding preserves the canonical interval
kernel. -/
noncomputable instance Slicing.IntervalCat.toLeftHeart_preservesKernel
    (s : Slicing C) {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0)
      (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  change IsLimit (FL.mapCone
    (KernelFork.ofι (kernel.ι f) (kernel.condition f)))
  exact (isLimitMapConeForkEquiv' FL (kernel.condition f)).symm <|
    IsLimit.ofIsoLimit (kernelIsKernel (FL.map f)) <|
      Fork.ext
        ((Slicing.IntervalCat.toLeftHeartKernelIso
          (C := C) (s := s) (a := a) (b := b) f).symm) (by
          have hι :
              (Slicing.IntervalCat.toLeftHeartKernelIso
                (C := C) (s := s) (a := a) (b := b) f).hom ≫
                kernel.ι (FL.map f) = FL.map (kernel.ι f) := by
            simpa [FL] using
              Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
                (C := C) (s := s) (a := a) (b := b) f
          change
            (Slicing.IntervalCat.toLeftHeartKernelIso
              (C := C) (s := s) (a := a) (b := b) f).inv ≫
              FL.map (kernel.ι f) = kernel.ι (FL.map f)
          rw [← hι]
          simp)

/-- The right adjacent-heart embedding preserves the canonical interval
cokernel. -/
noncomputable instance Slicing.IntervalCat.toRightHeart_preservesCokernel
    (s : Slicing C) {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0)
      (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  change IsColimit (FR.mapCocone
    (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)))
  exact (isColimitMapCoconeCoforkEquiv' FR (cokernel.condition f)).symm <|
    IsColimit.ofIsoColimit (cokernelIsCokernel (FR.map f)) <|
      Cofork.ext
        ((Slicing.IntervalCat.toRightHeartCokernelIso
          (C := C) (s := s) (a := a) (b := b) f).symm) (by
          have hπ : FR.map (cokernel.π f) ≫
                (Slicing.IntervalCat.toRightHeartCokernelIso
                  (C := C) (s := s) (a := a) (b := b) f).hom =
              cokernel.π (FR.map f) := by
            simpa [FR] using
              Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
                (C := C) (s := s) (a := a) (b := b) f
          change cokernel.π (FR.map f) ≫
              (Slicing.IntervalCat.toRightHeartCokernelIso
                (C := C) (s := s) (a := a) (b := b) f).inv =
            FR.map (cokernel.π f)
          rw [← hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id])

/-- An owner strict short exact sequence in a thin interval extends to an
ambient distinguished triangle. -/
theorem Slicing.IntervalCat.exists_distinguished_of_strictShortExact
    (s : Slicing C) {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧),
      Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  let tL := (s.phaseShift C a).toTStructure C
  letI := tL.hasHeartFullSubcategory
  letI : Abelian tL.heart.FullSubcategory := heartFullSubcategoryAbelian tL
  letI : CategoryWithHomology tL.heart.FullSubcategory :=
    categoryWithHomology_of_abelian
  let FL := Slicing.IntervalCat.toLeftHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  let tR := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := tR.hasHeartFullSubcategory
  letI : Abelian tR.heart.FullSubcategory := heartFullSubcategoryAbelian tR
  let FR := Slicing.IntervalCat.toRightHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  letI : Mono S.f := hS.shortExact.mono_f
  letI : Epi S.g := hS.shortExact.epi_g
  let h := hS.shortExact.exact.condition.choose
  let eKh : kernel S.g ≅ h.left.K :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.left.hi
  have heKh : eKh.inv ≫ kernel.ι S.g = h.left.i := by
    change (IsLimit.conePointUniqueUpToIso
      (kernelIsKernel S.g) h.left.hi).inv ≫ kernel.ι S.g = h.left.i
    exact IsLimit.conePointUniqueUpToIso_inv_comp
      (kernelIsKernel S.g) h.left.hi Limits.WalkingParallelPair.zero
  letI : Epi h.left.f' := hS.shortExact.exact.epi_f' h.left
  have hFRMono : Mono (FR.map h.left.f') := by
    letI : Mono (FR.map S.f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s S.f
        ⟨inferInstance, hS.strict_f⟩
    have hcomp : FR.map h.left.f' ≫ FR.map h.left.i = FR.map S.f := by
      calc
        FR.map h.left.f' ≫ FR.map h.left.i =
            FR.map (h.left.f' ≫ h.left.i) := by rw [← FR.map_comp]
        _ = FR.map S.f := by simp [h.left.f'_i]
    haveI : Mono (FR.map h.left.f' ≫ FR.map h.left.i) := by
      rw [hcomp]
      infer_instance
    exact mono_of_mono (FR.map h.left.f') (FR.map h.left.i)
  have hf'Strict : IsStrictMono h.left.f' :=
    Slicing.IntervalCat.strictMono_of_mono_toRightHeart C s h.left.f'
  letI : IsIso h.left.f' := hf'Strict.isIso
  let eK : S.X₁ ≅ kernel S.g := asIso h.left.f' ≪≫ eKh.symm
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    refine kernel.isoKernel S.g S.f eK ?_
    calc
      eK.hom ≫ kernel.ι S.g = h.left.f' ≫ h.left.i := by
        simp [eK, heKh, Category.assoc]
      _ = S.f := h.left.f'_i
  have hEpi : Epi (FL.map S.g) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s S.g
      ⟨inferInstance, hS.strict_g⟩
  have hKer : IsLimit
      (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  exact Slicing.IntervalCat.exists_distinguished_of_shortExact_toLeftHeart
    C s hL

/-- Owner strict short exact sequences in a thin interval are exactly the
short complexes whose ambient maps extend to a distinguished triangle. -/
theorem Slicing.IntervalCat.strictShortExact_iff_exists_distinguished
    (s : Slicing C) {S : ShortComplex (s.IntervalCat C a b)} :
    StrictShortExact S ↔
      ∃ (δ : S.X₃.obj ⟶ S.X₁.obj⟦(1 : ℤ)⟧),
        Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C := by
  constructor
  · exact Slicing.IntervalCat.exists_distinguished_of_strictShortExact C s
  · rintro ⟨δ, hT⟩
    exact Slicing.IntervalCat.strictShortExact_of_distinguished C s hT

/-- A strict short exact sequence in a thin interval supplies the expected
ambient owner Grothendieck-group relation. -/
theorem Slicing.IntervalCat.K₀_of_strictShortExact
    (s : Slicing C) {S : ShortComplex (s.IntervalCat C a b)}
    (hS : StrictShortExact S) :
    K₀.of C S.X₂.obj = K₀.of C S.X₁.obj + K₀.of C S.X₃.obj := by
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distinguished_of_strictShortExact C s hS
  simpa using K₀.of_triangle C (Triangle.mk S.f.hom S.g.hom δ) hT

/-- The fully faithful inclusion from a thin interval into a wider interval. -/
abbrev Slicing.IntervalCat.inclusion (s : Slicing C) {a₂ b₂ : ℝ}
    (ha : a₂ ≤ a) (hb : b ≤ b₂) :
    s.IntervalCat C a b ⥤ s.IntervalCat C a₂ b₂ :=
  ObjectProperty.ιOfLE (s.intervalProp_mono C ha hb)

set_option backward.isDefEq.respectTransparency false in
/-- A strict short exact sequence remains strict short exact after widening
the ambient thin interval. -/
theorem Slicing.IntervalCat.strictShortExact_inclusion
    (s : Slicing C) {a₂ b₂ : ℝ}
    [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (ha : a₂ ≤ a) (hb : b ≤ b₂)
    {S : ShortComplex (s.IntervalCat C a b)} (hS : StrictShortExact S) :
    StrictShortExact
      (S.map (Slicing.IntervalCat.inclusion C s ha hb)) := by
  obtain ⟨δ, hT⟩ :=
    Slicing.IntervalCat.exists_distinguished_of_strictShortExact C s hS
  have hT' :
      Triangle.mk
          ((S.map (Slicing.IntervalCat.inclusion C s ha hb)).f.hom)
          ((S.map (Slicing.IntervalCat.inclusion C s ha hb)).g.hom) δ ∈
        distTriang C := by
    simpa [Slicing.IntervalCat.inclusion] using hT
  exact Slicing.IntervalCat.strictShortExact_of_distinguished C s hT'

/-- Append a semistable strict quotient to an owner HN filtration of the
kernel object in a thin interval. -/
noncomputable def HNFiltration.appendStrictFactor
    {P : ℝ → ObjectProperty C} {s : Slicing C}
    {S : ShortComplex (s.IntervalCat C a b)}
    (G : HNFiltration C P S.X₁.obj) (hS : StrictShortExact S)
    (ψ : ℝ) (hψ : P ψ S.X₃.obj)
    (hψ_lt : ∀ j : Fin G.n, ψ < G.φ j) :
    HNFiltration C P S.X₂.obj := by
  let hδ := Slicing.IntervalCat.exists_distinguished_of_strictShortExact C s hS
  let δ := Classical.choose hδ
  have hT : Triangle.mk S.f.hom S.g.hom δ ∈ distTriang C :=
    Classical.choose_spec hδ
  exact G.appendFactor C (Triangle.mk S.f.hom S.g.hom δ) hT
    (Iso.refl _) (Iso.refl _) ψ hψ hψ_lt

/-- Open slicing intervals are closed under binary products. -/
instance Slicing.intervalProp_isClosedUnderBinaryProducts (s : Slicing C) :
    (s.intervalProp C a b).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (s.intervalProp C a b).prop_of_iso ?_
      (s.intervalProp_of_triangle C
        (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩)
        (binaryProductTriangle_distinguished _ _))
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/-- Open slicing intervals are closed under finite products. -/
instance Slicing.intervalProp_isClosedUnderFiniteProducts (s : Slicing C) :
    (s.intervalProp C a b).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Thin interval categories have finite products. -/
noncomputable instance Slicing.intervalCat_hasFiniteProducts
    (s : Slicing C) : HasFiniteProducts (s.IntervalCat C a b) := by
  infer_instance

/-- Thin interval categories have binary biproducts. -/
noncomputable instance Slicing.intervalCat_hasBinaryBiproducts
    (s : Slicing C) : HasBinaryBiproducts (s.IntervalCat C a b) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Thin interval categories have finite biproducts. -/
noncomputable instance Slicing.intervalCat_hasFiniteBiproducts
    (s : Slicing C) : HasFiniteBiproducts (s.IntervalCat C a b) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Thin interval categories have equalizers. -/
noncomputable instance Slicing.intervalCat_hasEqualizers
    (s : Slicing C) : HasEqualizers (s.IntervalCat C a b) :=
  Preadditive.hasEqualizers_of_hasKernels

/-- Thin interval categories have coequalizers. -/
noncomputable instance Slicing.intervalCat_hasCoequalizers
    (s : Slicing C) : HasCoequalizers (s.IntervalCat C a b) :=
  Preadditive.hasCoequalizers_of_hasCokernels

/-- Thin interval categories have pullbacks. -/
noncomputable instance Slicing.intervalCat_hasPullbacks
    (s : Slicing C) : HasPullbacks (s.IntervalCat C a b) :=
  Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers _

/-- Thin interval categories have pushouts. -/
noncomputable instance Slicing.intervalCat_hasPushouts
    (s : Slicing C) : HasPushouts (s.IntervalCat C a b) :=
  Limits.hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers _

/-- The left adjacent-heart embedding preserves finite limits. -/
noncomputable instance Slicing.IntervalCat.toLeftHeart_preservesFiniteLimits
    (s : Slicing C) : PreservesFiniteLimits
      (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- The right adjacent-heart embedding preserves finite colimits. -/
noncomputable instance Slicing.IntervalCat.toRightHeart_preservesFiniteColimits
    (s : Slicing C) : PreservesFiniteColimits
      (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)) := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Finiteness of the subobject lattice in the left adjacent heart descends
to the thin interval category. -/
theorem Slicing.IntervalCat.finite_subobject_of_leftHeart (s : Slicing C)
    {X : s.IntervalCat C a b}
    (hX : Finite (Subobject
      ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)).obj X))) : Finite (Subobject X) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  exact Finite.subobject_of_fullFaithful_preservesMono
    (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)) hX

/-- An Artinian object in the left adjacent heart is Artinian in the thin
interval category. -/
theorem Slicing.IntervalCat.isArtinianObject_of_leftHeart (s : Slicing C)
    {X : s.IntervalCat C a b}
    [IsArtinianObject
      ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)).obj X)] : IsArtinianObject X := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  exact isArtinianObject_of_fullFaithful_preservesMono
    (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1))

/-- A Noetherian object in the left adjacent heart is Noetherian in the thin
interval category. -/
theorem Slicing.IntervalCat.isNoetherianObject_of_leftHeart (s : Slicing C)
    {X : s.IntervalCat C a b}
    [IsNoetherianObject
      ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)).obj X)] : IsNoetherianObject X := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  exact isNoetherianObject_of_fullFaithful_preservesMono
    (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1))

/-- An Artinian object in the right adjacent heart is strict-Artinian in the
thin interval category. -/
theorem Slicing.IntervalCat.isStrictArtinianObject_of_rightHeart
    (s : Slicing C) {X : s.IntervalCat C a b}
    [IsArtinianObject
      ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)).obj X)] : IsStrictArtinianObject X := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  exact isStrictArtinianObject_of_fullFaithful_map_strictMono FR
    (fun f hf ↦ by
      letI : Mono (FR.map f) :=
        Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s f hf
      exact isStrictMono_of_mono (FR.map f))

/-- A Noetherian object in the right adjacent heart is strict-Noetherian in
the thin interval category. -/
theorem Slicing.IntervalCat.isStrictNoetherianObject_of_rightHeart
    (s : Slicing C) {X : s.IntervalCat C a b}
    [IsNoetherianObject
      ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
        (Fact.out : b - a ≤ 1)).obj X)] : IsStrictNoetherianObject X := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart
    (C := C) (s := s) a b (Fact.out : b - a ≤ 1)
  exact isStrictNoetherianObject_of_fullFaithful_map_strictMono FR
    (fun f hf ↦ by
      letI : Mono (FR.map f) :=
        Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s f hf
      exact isStrictMono_of_mono (FR.map f))

/-- A thin owner slicing interval is quasi-abelian. -/
noncomputable instance Slicing.intervalCat_quasiAbelian (s : Slicing C) :
    QuasiAbelian (s.IntervalCat C a b) where
  pullback_strictEpi := by
    intro X Y Z f g hg
    let t := (s.phaseShift C a).toTStructure C
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
    let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    haveI : Epi (FL.map g) :=
      Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s g hg
    have hpb : IsLimit
        (PullbackCone.mk
          (FL.map (pullback.fst f g))
          (FL.map (pullback.snd f g))
          (by
            have h := congrArg FL.map
              (pullback.condition (f := f) (g := g))
            simpa using h) :
          PullbackCone (FL.map f) (FL.map g)) :=
      isLimitOfHasPullbackOfPreservesLimit FL f g
    haveI : Epi (FL.map (pullback.fst f g)) :=
      CategoryTheory.Abelian.epi_fst_of_isLimit
        (f := FL.map f) (g := FL.map g) hpb
    exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart C s
      (pullback.fst f g)
  pushout_strictMono := by
    intro X Y Z f g hf
    let t := (s.phaseShift C (b - 1)).toDualTStructure C
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
    let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)
    haveI : Mono (FR.map f) :=
      Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s f hf
    have hpo : IsColimit
        (PushoutCocone.mk
          (FR.map (pushout.inl f g))
          (FR.map (pushout.inr f g))
          (by
            have h := congrArg FR.map
              (pushout.condition (f := f) (g := g))
            simpa using h) :
          PushoutCocone (FR.map f) (FR.map g)) :=
      isColimitOfHasPushoutOfPreservesColimit FR f g
    haveI : Mono (FR.map (pushout.inr f g)) :=
      CategoryTheory.Abelian.mono_inr_of_isColimit
        (f := FR.map f) (g := FR.map g) hpo
    exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart C s
      (pushout.inr f g)

end

end CategoryTheory.Triangulated
