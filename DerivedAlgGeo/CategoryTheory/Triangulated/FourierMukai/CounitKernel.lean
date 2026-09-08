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

`Φ_{Q * P} ⟶ Φ_{O_Δ}`.

The missing geometric statement is that this natural transformation is
induced by an actual kernel morphism `Q * P ⟶ O_Δ`.  `CounitKernelConeData`
records precisely that morphism, its dg cone, and the equality identifying its
transform with the counit.  Exactness in the kernel variable then sends the dg
cone to a pointwise distinguished triangle whose third functor is the
Fourier--Mukai twist candidate.

Nothing here derives the kernel arrow.  That is a genuine Fourier--Mukai
realization theorem (using the convolution formula, the diagonal kernel, and
the adjunction trace), and remains an explicit geometric obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vX vY v₁ v₂ vK uX uY u₁ u₂ uK

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

variable {X : Type uX} {Y : Type uY}
  {W₁ : Type u₁} {W₂ : Type u₂} {K : Type uK}
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{v₁} W₁] [Category.{v₂} W₂]
  [DGCategory.{vK} K] [IsPretriangulated K]

/-- A dg kernel arrow realizing the counit of a kernel-presented adjunction,
together with a chosen cone of that arrow.

The equality `transform_arrow` includes both necessary changes of
presentation: convolution identifies the source transform with `Φ_Q ⋙ Φ_P`,
and the unit-kernel isomorphism identifies the target transform with `id_Y`.
-/
structure CounitKernelConeData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence Y Y (H0 K)) (P : W₁)
    (R : RightAdjointKernelData C C' P)
    (D : ConvolutionData C' C E) (U : UnitKernelData E) where
  /-- The closed kernel morphism `Q * P ⟶ O_Δ`. -/
  arrow : cocycles (H0.of K (D.conv R.adjKernel P))
    (H0.of K U.unitKernel)
  /-- Its chosen dg cone. -/
  cone : K
  /-- The cone representability witness. -/
  isCone : IsConeOf arrow.1 cone
  /-- Transforming the kernel arrow gives the adjunction counit after the
  convolution and unit-kernel identifications. -/
  transform_arrow :
    E.transformMap (H0.homMk arrow) =
      (D.compIso R.adjKernel P).inv ≫ R.adj.counit ≫ U.unitIso.hom

namespace CounitKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y (H0 K)} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : CounitKernelConeData C C' E P R D U)

/-- The kernel arrow and its cone as a reusable dg cone presentation. -/
def presentation : DGCategory.ConePresentation K where
  source := H0.of K (D.conv R.adjKernel P)
  target := H0.of K U.unitKernel
  arrow := S.arrow
  cone := S.cone
  isCone := S.isCone

@[simp]
omit [IsPretriangulated K] in
theorem presentation_source :
    S.presentation.source = H0.of K (D.conv R.adjKernel P) :=
  rfl

@[simp]
omit [IsPretriangulated K] in
theorem presentation_target :
    S.presentation.target = H0.of K U.unitKernel :=
  rfl

@[simp]
omit [IsPretriangulated K] in
theorem presentation_cone : S.presentation.cone = S.cone :=
  rfl

/-- The Fourier--Mukai transform of the counit-cone kernel.  This is the
kernel-presented twist candidate. -/
abbrev twist : Y ⥤ Y := E.transform S.cone

section Exact

variable [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  (hE : E.KernelEvaluationExact)

/-- The counit-kernel cone as a source-natural family of transform triangles.
The first two vertices are the convolution and unit transforms; the third is
`S.twist`. -/
noncomputable def triangleInSource : Y ⥤ Triangle Y :=
  hE.coneTriangleInSource S.presentation

@[simp]
theorem triangleInSource_obj₁ (A : Y) :
    ((S.triangleInSource hE).obj A).obj₁ =
      (E.transform (D.conv R.adjKernel P)).obj A :=
  rfl

@[simp]
theorem triangleInSource_obj₂ (A : Y) :
    ((S.triangleInSource hE).obj A).obj₂ =
      (E.transform U.unitKernel).obj A :=
  rfl

@[simp]
theorem triangleInSource_obj₃ (A : Y) :
    ((S.triangleInSource hE).obj A).obj₃ = S.twist.obj A :=
  rfl

/-- Every objectwise triangle obtained from the counit-kernel cone is
distinguished. -/
theorem triangleInSource_obj_distinguished (A : Y) :
    (S.triangleInSource hE).obj A ∈ distTriang Y :=
  hE.coneTriangleInSource_obj_distinguished S.presentation A

end Exact

end CounitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
