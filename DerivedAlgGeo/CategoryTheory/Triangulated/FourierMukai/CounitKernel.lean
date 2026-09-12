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
induced by an actual kernel morphism `conv Q P ⟶ O_Δ`.  `CounitKernelData`
records that ordinary kernel arrow and the equality identifying its transform
with the counit.  Any enhancement of the kernel category then supplies a
noncanonical closed representative and a noncanonical dg cone, packaged by
`CounitKernelData.toConeData`.  Exactness in the kernel variable sends that dg
cone to a pointwise distinguished triangle whose third functor is the
Fourier--Mukai twist candidate.

The constructor `CounitKernelData.ofFull` produces the ordinary arrow when the
kernel transform is explicitly assumed full.  No fullness theorem is asserted
here: without that strong hypothesis, producing the kernel arrow remains the
genuine Fourier--Mukai realization obligation involving convolution, the
diagonal kernel, and the adjunction trace.
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

/-- An ordinary kernel arrow realizing the counit of a kernel-presented
adjunction, together with the exact comparison between its transform and the
counit.  It deliberately contains no enhancement or cone choice. -/
structure CounitKernelData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence Y Y W) (P : W₁)
    (R : RightAdjointKernelData C C' P)
    (D : ConvolutionData C' C E) (U : UnitKernelData E) where
  /-- The kernel morphism `conv Q P ⟶ O_Δ`. -/
  arrow : D.conv R.adjKernel P ⟶ U.unitKernel
  /-- Transforming the kernel morphism gives the adjunction counit after the
  convolution and unit-kernel identifications. -/
  transform_arrow :
    E.transformMap arrow =
      (D.compIso R.adjKernel P).inv ≫ R.adj.counit ≫ U.unitIso.hom

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

namespace CounitKernelData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : CounitKernelData C C' E P R D U)

/-- Ordinary counit-kernel data are determined by their kernel arrow. -/
@[ext]
theorem ext {S T : CounitKernelData C C' E P R D U}
    (h : S.arrow = T.arrow) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- Fullness of the kernel transform is a sufficient abstract hypothesis for
lifting the adjunction counit comparison to an ordinary kernel morphism. -/
noncomputable def ofFull [E.kernelTransform.Full] :
    CounitKernelData C C' E P R D U where
  arrow := E.kernelTransform.preimage
    ((D.compIso R.adjKernel P).inv ≫ R.adj.counit ≫ U.unitIso.hom)
  transform_arrow := E.kernelTransform.map_preimage _

/-- A noncanonical closed degree-zero representative of the ordinary kernel
arrow in an enhancement. -/
noncomputable def liftedArrow (e : Enhancement.{vE, uE} W) : cocycles
    (show e.dgCat from e.equiv.inverse.obj (D.conv R.adjKernel P))
    (show e.dgCat from e.equiv.inverse.obj U.unitKernel) :=
  (Z0.toH0 e.dgCat).preimage (e.equiv.inverse.map S.arrow)

/-- The selected cocycle represents the inverse image of the ordinary kernel
arrow in `H⁰` of the enhancement. -/
@[simp]
theorem homMk_liftedArrow (e : Enhancement.{vE, uE} W) :
    H0.homMk (C := e.dgCat) (S.liftedArrow e) =
      e.equiv.inverse.map S.arrow :=
  (Z0.toH0 e.dgCat).map_preimage _

/-- Conjugating the selected representative by the counit of the enhancement
equivalence recovers the original kernel arrow. -/
theorem counit_conjugate_liftedArrow (e : Enhancement.{vE, uE} W) :
    (e.equiv.counitIso.app (D.conv R.adjKernel P)).inv ≫
        e.equiv.functor.map (H0.homMk (C := e.dgCat) (S.liftedArrow e)) ≫
        (e.equiv.counitIso.app U.unitKernel).hom =
      S.arrow := by
  rw [S.homMk_liftedArrow e]
  rw [← cancel_epi
    (e.equiv.counitIso.app (D.conv R.adjKernel P)).hom,
    Iso.hom_inv_id_assoc]
  exact e.equiv.counit_naturality S.arrow

/-- Choose a closed representative and a dg cone for an ordinary counit kernel
arrow.  Both choices are noncanonical; the resulting comparison equation is
the exact equation stored in `S`. -/
noncomputable def toConeData (e : Enhancement.{vE, uE} W) :
    CounitKernelConeData C C' E e P R D U := by
  let hcone := IsPretriangulated.exists_cone
    (S.liftedArrow e).1 (S.liftedArrow e).2
  refine
    { arrow := S.liftedArrow e
      cone := hcone.choose
      isCone := hcone.choose_spec.some
      transform_arrow := ?_ }
  exact (congrArg E.transformMap (S.counit_conjugate_liftedArrow e)).trans
    S.transform_arrow

end CounitKernelData

namespace CounitKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : CounitKernelConeData C C' E e P R D U)

/-- Forget the chosen cocycle and cone while retaining the ordinary kernel
arrow represented through the enhancement equivalence. -/
def toCounitKernelData : CounitKernelData C C' E P R D U where
  arrow := (e.equiv.counitIso.app (D.conv R.adjKernel P)).inv ≫
    e.equiv.functor.map (H0.homMk (C := e.dgCat) S.arrow) ≫
    (e.equiv.counitIso.app U.unitKernel).hom
  transform_arrow := S.transform_arrow

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

namespace CounitKernelData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : CounitKernelData C C' E P R D U)

/-- Forgetting the choices made by `toConeData` recovers the original ordinary
kernel datum.  This does not identify the selected cocycle or cone. -/
@[simp]
theorem toConeData_toCounitKernelData (e : Enhancement.{vE, uE} W) :
    (S.toConeData e).toCounitKernelData = S := by
  apply CounitKernelData.ext
  exact S.counit_conjugate_liftedArrow e

end CounitKernelData

end CategoryTheory.Triangulated.FourierMukai
