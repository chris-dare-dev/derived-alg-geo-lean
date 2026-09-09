/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Autoequivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.KernelCone

/-!
# Kernel realizations of adjunction counits

Let `Φ_P : X ⥤ Y` have a kernel-presented right adjoint `Φ_Q`.  With a
convolution kernel and a unit kernel on `Y`, the counit has the form

`Φ_{conv Q P} ⟶ Φ_{O_Δ}`.

Here `conv Q P` is the kernel of `Φ_Q ⋙ Φ_P` (`ConvolutionData.compIso`
reads composition diagrammatically, so this is Huybrechts' `P ∘ Q`).

The missing geometric statement is that this natural transformation is
induced by an actual kernel morphism `conv Q P ⟶ O_Δ`, and that the kernel
category is enhanced so that the morphism has a dg cone.  `CounitKernelConeData`
records precisely that: for an enhancement `e` of the kernel category, a
closed dg arrow between the enhancement's lifts of the two kernels, its chosen
cone, and the equality identifying its transform with the counit after the
comparison equivalence.  Exactness in the kernel variable then sends the dg
cone to a pointwise distinguished triangle whose third functor is the
Fourier--Mukai twist candidate.

Nothing here derives the kernel arrow.  That is a genuine Fourier--Mukai
realization theorem (using the convolution formula, the diagonal kernel, and
the adjunction trace), and remains an explicit geometric obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vX vY v₁ v₂ vW vE uX uY u₁ u₂ uW uE

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

variable {X : Type uX} {Y : Type uY}
  {W₁ : Type u₁} {W₂ : Type u₂} {W : Type uW}
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{v₁} W₁] [Category.{v₂} W₂] [Category.{vW} W]

/-- A dg kernel arrow realizing the counit of a kernel-presented adjunction,
together with a chosen cone of that arrow, for an enhancement `e` of the
kernel category.

The arrow lives between the enhancement's lifts `e.equiv.inverse.obj _` of
the convolution kernel and the unit kernel.  The equality `transform_arrow`
includes all the changes of presentation: the comparison equivalence
identifies the transform of the arrow with a map between the two kernels,
convolution identifies the source transform with `Φ_Q ⋙ Φ_P`, and the
unit-kernel isomorphism identifies the target transform with `𝟭 Y`. -/
structure CounitKernelConeData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence Y Y W) (e : Enhancement.{vE, uE} W) (P : W₁)
    (R : RightAdjointKernelData C C' P)
    (D : ConvolutionData C' C E) (U : UnitKernelData E) where
  /-- The closed kernel morphism `conv Q P ⟶ O_Δ`, in the enhancement. -/
  arrow : cocycles
    (H0.of e.dgCat (e.equiv.inverse.obj (D.conv R.adjKernel P)))
    (H0.of e.dgCat (e.equiv.inverse.obj U.unitKernel))
  /-- Its chosen dg cone. -/
  cone : e.dgCat
  /-- The cone representability witness. -/
  isCone : IsConeOf arrow.1 cone
  /-- Transforming the kernel arrow gives the adjunction counit after the
  enhancement, convolution and unit-kernel identifications. -/
  transform_arrow :
    E.transformMap
        ((e.equiv.counitIso.app (D.conv R.adjKernel P)).inv ≫
          e.equiv.functor.map (H0.homMk (C := e.dgCat) arrow) ≫
          (e.equiv.counitIso.app U.unitKernel).hom) =
      (D.compIso R.adjKernel P).inv ≫ R.adj.counit ≫ U.unitIso.hom

namespace CounitKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : CounitKernelConeData C C' E e P R D U)

/-- The kernel arrow and its cone as a reusable dg cone presentation. -/
def presentation : DGCategory.ConePresentation e.dgCat where
  source := H0.of e.dgCat (e.equiv.inverse.obj (D.conv R.adjKernel P))
  target := H0.of e.dgCat (e.equiv.inverse.obj U.unitKernel)
  arrow := S.arrow
  cone := S.cone
  isCone := S.isCone

@[simp]
theorem presentation_source :
    S.presentation.source =
      H0.of e.dgCat (e.equiv.inverse.obj (D.conv R.adjKernel P)) :=
  rfl

@[simp]
theorem presentation_target :
    S.presentation.target = H0.of e.dgCat (e.equiv.inverse.obj U.unitKernel) :=
  rfl

@[simp]
theorem presentation_cone : S.presentation.cone = S.cone :=
  rfl

/-- The Fourier--Mukai transform of the counit-cone kernel, read in the kernel
category through the enhancement.  This is the kernel-presented twist
candidate. -/
abbrev twist : Y ⥤ Y :=
  E.transform (e.equiv.functor.obj (show H0 e.dgCat from S.cone))

section Exact

variable [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ] (hE : E.KernelEvaluationExact)

/-- The counit-kernel cone as a source-natural family of transform triangles.
The first two vertices are the transforms of the enhancement's lifts of the
convolution and unit kernels; the third is `S.twist`. -/
noncomputable def triangleInSource : Y ⥤ Triangle Y :=
  hE.coneTriangleInSource e S.presentation

@[simp]
theorem triangleInSource_obj₁ (A : Y) :
    ((S.triangleInSource hE).obj A).obj₁ =
      (E.transform (e.equiv.functor.obj
        (e.equiv.inverse.obj (D.conv R.adjKernel P)))).obj A :=
  rfl

@[simp]
theorem triangleInSource_obj₂ (A : Y) :
    ((S.triangleInSource hE).obj A).obj₂ =
      (E.transform (e.equiv.functor.obj
        (e.equiv.inverse.obj U.unitKernel))).obj A :=
  rfl

@[simp]
theorem triangleInSource_obj₃ (A : Y) :
    ((S.triangleInSource hE).obj A).obj₃ = S.twist.obj A :=
  rfl

/-- Every objectwise triangle obtained from the counit-kernel cone is
distinguished. -/
theorem triangleInSource_obj_distinguished [e.equiv.functor.IsTriangulated] (A : Y) :
    (S.triangleInSource hE).obj A ∈ distTriang Y :=
  hE.coneTriangleInSource_obj_distinguished e S.presentation A

end Exact

end CounitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
