/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.TwoHeartEmbedding

/-!
# Kernels and cokernels in owner interval categories

A thin slicing interval computes its kernels in the left adjacent abelian
heart and its cokernels in the right adjacent abelian heart.  The two-heart
closure results ensure that these ambient objects remain in the interval;
full faithfulness then transports the universal properties back.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.TStructure
open CategoryTheory.Triangulated.TStructure

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

section

variable {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- A morphism in a thin owner interval has a kernel, computed in the left
adjacent abelian heart. -/
theorem Slicing.intervalCat_hasKernel (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) : HasKernel f := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (s := s) (C := C) a b
    (Fact.out : b - a ≤ 1)
  let XH : t.heart.FullSubcategory := FL.obj X
  let YH : t.heart.FullSubcategory := FL.obj Y
  let fH : XH ⟶ YH := FL.map f
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    s.intervalProp_of_mono_leftHeart C (Fact.out : a < b) X.property
      (kernel.ι fH)
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    ext
    exact congr_arg (·.hom) (kernel.condition fH)
  refine ⟨⟨KernelFork.ofι k hk_zero, ?_⟩⟩
  refine KernelFork.IsLimit.ofι _ _ (fun {W} g hg ↦ ?_)
    (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
  · let WH : t.heart.FullSubcategory := FL.obj W
    let gH : WH ⟶ XH := FL.map g
    have hgH : gH ≫ fH = 0 := by
      apply t.ιHeart.map_injective
      change g.hom ≫ f.hom = 0
      exact congr_arg (·.hom) hg
    exact ObjectProperty.homMk (kernel.lift fH gH hgH).hom
  · let WH : t.heart.FullSubcategory := FL.obj W
    let gH : WH ⟶ XH := FL.map g
    have hgH : gH ≫ fH = 0 := by
      apply t.ιHeart.map_injective
      change g.hom ≫ f.hom = 0
      exact congr_arg (·.hom) hg
    ext
    exact congr_arg (·.hom) (kernel.lift_ι fH gH hgH)
  · let WH : t.heart.FullSubcategory := FL.obj W
    let gH : WH ⟶ XH := FL.map g
    have hgH : gH ≫ fH = 0 := by
      apply t.ιHeart.map_injective
      change g.hom ≫ f.hom = 0
      exact congr_arg (·.hom) hg
    let mH : WH ⟶ kernel fH := ObjectProperty.homMk m.hom
    have hmH : mH ≫ kernel.ι fH = kernel.lift fH gH hgH ≫ kernel.ι fH := by
      ext
      rw [show (kernel.lift fH gH hgH ≫ kernel.ι fH).hom = gH.hom by
        exact congr_arg (·.hom) (kernel.lift_ι fH gH hgH)]
      change m.hom ≫ k.hom = g.hom
      exact congr_arg (·.hom) hm
    have hmEq : mH = kernel.lift fH gH hgH :=
      Fork.IsLimit.hom_ext (kernelIsKernel fH) hmH
    ext
    exact congr_arg (·.hom) hmEq

/-- Thin owner interval categories have all kernels. -/
noncomputable instance Slicing.intervalCat_hasKernels (s : Slicing C) :
    HasKernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ s.intervalCat_hasKernel C (X := X) (Y := Y) f⟩

/-- A morphism in a thin owner interval has a cokernel, computed in the right
adjacent abelian heart. -/
theorem Slicing.intervalCat_hasCokernel (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) : HasCokernel f := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (s := s) (C := C) a b
    (Fact.out : b - a ≤ 1)
  let XH : t.heart.FullSubcategory := FR.obj X
  let YH : t.heart.FullSubcategory := FR.obj Y
  let fH : XH ⟶ YH := FR.map f
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.intervalProp_of_epi_rightHeart C (Fact.out : a < b) Y.property
      (cokernel.π fH)
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    ext
    exact congr_arg (·.hom) (cokernel.condition fH)
  refine ⟨⟨CokernelCofork.ofπ p hp_zero, ?_⟩⟩
  refine CokernelCofork.IsColimit.ofπ _ _ (fun {W} g hg ↦ ?_)
    (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
  · let WH : t.heart.FullSubcategory := FR.obj W
    let gH : YH ⟶ WH := FR.map g
    have hgH : fH ≫ gH = 0 := by
      apply t.ιHeart.map_injective
      change f.hom ≫ g.hom = 0
      exact congr_arg (·.hom) hg
    exact ObjectProperty.homMk (cokernel.desc fH gH hgH).hom
  · let WH : t.heart.FullSubcategory := FR.obj W
    let gH : YH ⟶ WH := FR.map g
    have hgH : fH ≫ gH = 0 := by
      apply t.ιHeart.map_injective
      change f.hom ≫ g.hom = 0
      exact congr_arg (·.hom) hg
    ext
    exact congr_arg (·.hom) (cokernel.π_desc fH gH hgH)
  · let WH : t.heart.FullSubcategory := FR.obj W
    let gH : YH ⟶ WH := FR.map g
    have hgH : fH ≫ gH = 0 := by
      apply t.ιHeart.map_injective
      change f.hom ≫ g.hom = 0
      exact congr_arg (·.hom) hg
    let mH : cokernel fH ⟶ WH := ObjectProperty.homMk m.hom
    have hmH : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH gH hgH := by
      ext
      rw [show (cokernel.π fH ≫ cokernel.desc fH gH hgH).hom = gH.hom by
        exact congr_arg (·.hom) (cokernel.π_desc fH gH hgH)]
      change p.hom ≫ m.hom = g.hom
      exact congr_arg (·.hom) hm
    have hmEq : mH = cokernel.desc fH gH hgH :=
      Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hmH
    ext
    exact congr_arg (·.hom) hmEq

/-- Thin owner interval categories have all cokernels. -/
noncomputable instance Slicing.intervalCat_hasCokernels (s : Slicing C) :
    HasCokernels (s.IntervalCat C a b) :=
  ⟨fun {X Y} f ↦ s.intervalCat_hasCokernel C (X := X) (Y := Y) f⟩

end

end CategoryTheory.Triangulated
