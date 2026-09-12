/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Autoequivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.KernelTransformation

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
cone to a source-natural family of pointwise distinguished triangles.
`CounitKernelConeData.counitTriangleInSource` transports their first two
vertices to the composite adjoint transform and the identity functor, with
first map literally the adjunction counit and third vertex the Fourier--Mukai
twist candidate.

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

/-- Read counit-kernel data through the generic kernel-transformation
realization interface. -/
def toKernelTransformationData :
    KernelTransformationData E (D.conv R.adjKernel P) U.unitKernel
      (C'.transform R.adjKernel ⋙ C.transform P) (Functor.id Y)
      (D.compIso R.adjKernel P).symm U.unitIso.symm R.adj.counit where
  arrow := S.arrow
  transform_arrow := S.transform_arrow

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
    CounitKernelData C C' E P R D U := by
  let T := KernelTransformationData.ofFull (E := E)
    (K := D.conv R.adjKernel P) (L := U.unitKernel)
    (sourceIso := (D.compIso R.adjKernel P).symm)
    (targetIso := U.unitIso.symm) (α := R.adj.counit)
  exact
    { arrow := T.arrow
      transform_arrow := T.transform_arrow }

/-- A noncanonical closed degree-zero representative of the ordinary kernel
arrow in an enhancement. -/
noncomputable def liftedArrow (e : Enhancement.{vE, uE} W) : cocycles
    (show e.dgCat from e.equiv.inverse.obj (D.conv R.adjKernel P))
    (show e.dgCat from e.equiv.inverse.obj U.unitKernel) :=
  e.liftedCocycle S.arrow

/-- The selected cocycle represents the inverse image of the ordinary kernel
arrow in `H⁰` of the enhancement. -/
@[simp]
theorem homMk_liftedArrow (e : Enhancement.{vE, uE} W) :
    H0.homMk (C := e.dgCat) (S.liftedArrow e) =
      e.equiv.inverse.map S.arrow :=
  e.homMk_liftedCocycle S.arrow

/-- Conjugating the selected representative by the counit of the enhancement
equivalence recovers the original kernel arrow. -/
theorem counit_conjugate_liftedArrow (e : Enhancement.{vE, uE} W) :
    (e.equiv.counitIso.app (D.conv R.adjKernel P)).inv ≫
        e.equiv.functor.map (H0.homMk (C := e.dgCat) (S.liftedArrow e)) ≫
        (e.equiv.counitIso.app U.unitKernel).hom =
      S.arrow :=
  e.counit_conjugate_liftedCocycle S.arrow

/-- Choose a closed representative and a dg cone for an ordinary counit kernel
arrow.  Both choices are noncanonical; the resulting comparison equation is
the exact equation stored in `S`. -/
noncomputable def toConeData (e : Enhancement.{vE, uE} W) :
    CounitKernelConeData C C' E e P R D U := by
  let T := S.toKernelTransformationData.toConeData e
  exact
    { arrow := T.arrow
      cone := T.cone
      isCone := T.isCone
      transform_arrow := T.transform_arrow }

end CounitKernelData

namespace CounitKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : CounitKernelConeData C C' E e P R D U)

/-- Read enhanced counit-kernel data through the generic
kernel-transformation realization interface. -/
def toKernelTransformationConeData :
    KernelTransformationConeData E e (D.conv R.adjKernel P) U.unitKernel
      (C'.transform R.adjKernel ⋙ C.transform P) (Functor.id Y)
      (D.compIso R.adjKernel P).symm U.unitIso.symm R.adj.counit where
  arrow := S.arrow
  cone := S.cone
  isCone := S.isCone
  transform_arrow := S.transform_arrow

/-- Forget the chosen cocycle and cone while retaining the ordinary kernel
arrow represented through the enhancement equivalence. -/
def toCounitKernelData : CounitKernelData C C' E P R D U where
  arrow := S.toKernelTransformationConeData.toKernelTransformationData.arrow
  transform_arrow :=
    S.toKernelTransformationConeData.toKernelTransformationData.transform_arrow

/-- The kernel arrow and its cone as a reusable dg cone presentation. -/
def presentation : DGCategory.ConePresentation e.dgCat where
  source := S.toKernelTransformationConeData.presentation.source
  target := S.toKernelTransformationConeData.presentation.target
  arrow := S.toKernelTransformationConeData.presentation.arrow
  cone := S.toKernelTransformationConeData.presentation.cone
  isCone := S.toKernelTransformationConeData.presentation.isCone

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

/-- Identify the enhanced lift of the convolution kernel first with the
ordinary convolution kernel and then with the composite transform presenting
the source of the adjunction counit. -/
def sourceTransformIso (_S : CounitKernelConeData C C' E e P R D U) :
    E.transform (e.equiv.functor.obj
      (H0.of e.dgCat
        (e.equiv.inverse.obj (D.conv R.adjKernel P)))) ≅
      C'.transform R.adjKernel ⋙ C.transform P :=
  _S.toKernelTransformationConeData.sourceTransformIso

/-- Identify the enhanced lift of the unit kernel with the identity transform,
using the enhancement comparison and the supplied unit-kernel presentation. -/
def targetTransformIso (_S : CounitKernelConeData C C' E e P R D U) :
    E.transform (e.equiv.functor.obj
      (H0.of e.dgCat (e.equiv.inverse.obj U.unitKernel))) ≅ Functor.id Y :=
  _S.toKernelTransformationConeData.targetTransformIso

@[simp]
theorem sourceTransformIso_hom :
    S.sourceTransformIso.hom =
      E.transformMap (e.equiv.counitIso.app
        (D.conv R.adjKernel P)).hom ≫
        (D.compIso R.adjKernel P).inv :=
  S.toKernelTransformationConeData.sourceTransformIso_hom

@[simp]
theorem targetTransformIso_hom :
    S.targetTransformIso.hom =
      E.transformMap (e.equiv.counitIso.app U.unitKernel).hom ≫
        U.unitIso.inv :=
  S.toKernelTransformationConeData.targetTransformIso_hom

/-- The stored kernel-transform equation, normalized to the naturality square
whose bottom edge is literally the adjunction counit. -/
theorem transform_arrow_counit_square :
    E.transformMap (e.equiv.functor.map
        (H0.homMk (C := e.dgCat) S.arrow)) ≫
        S.targetTransformIso.hom =
      S.sourceTransformIso.hom ≫ R.adj.counit :=
  S.toKernelTransformationConeData.transform_arrow_square

/-- The generic endpoint-normalization package underlying the literal counit
triangle. -/
def normalizationData :
    E.KernelConeNormalizationData e S.presentation
      (C'.transform R.adjKernel ⋙ C.transform P) (Functor.id Y)
      R.adj.counit :=
  S.toKernelTransformationConeData.normalizationData

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
  S.normalizationData.rawTriangle hE

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

/-- The first map of the raw transform triangle before endpoint
normalization. -/
theorem triangleInSource_mor₁ :
    Functor.whiskerLeft (S.triangleInSource hE) Triangle.π₁Toπ₂ =
      E.transformMap (e.equiv.functor.map
        (H0.homMk (C := e.dgCat) S.arrow)) :=
  S.normalizationData.rawTriangle_mor₁ hE

/-- The source endpoint comparison, typed against the first projection of the
raw triangle functor. -/
noncomputable def triangleInSourceObj₁Iso :
    S.triangleInSource hE ⋙ Triangle.π₁ ≅
      C'.transform R.adjKernel ⋙ C.transform P :=
  S.normalizationData.rawTriangleObj₁Iso hE

/-- The target endpoint comparison, typed against the second projection of
the raw triangle functor. -/
noncomputable def triangleInSourceObj₂Iso :
    S.triangleInSource hE ⋙ Triangle.π₂ ≅ Functor.id Y :=
  S.normalizationData.rawTriangleObj₂Iso hE

/-- The first square for the comparison from the raw transform triangle to the
literal counit triangle. -/
theorem triangleInSource_counit_square :
    Functor.whiskerLeft (S.triangleInSource hE) Triangle.π₁Toπ₂ ≫
        (S.triangleInSourceObj₂Iso hE).hom =
      (S.triangleInSourceObj₁Iso hE).hom ≫ R.adj.counit :=
  S.normalizationData.rawTriangle_square hE

/-- The transported second map from the identity functor to the twist
candidate.  It retains the supplied enhancement and cone choices. -/
noncomputable def counitToTwist : Functor.id Y ⟶ S.twist :=
  S.normalizationData.normalizedSecond hE

/-- The transported connecting map from the twist candidate to the shifted
composite of the right adjoint and the original transform. -/
noncomputable def twistToShiftedComposite :
    S.twist ⟶
      (C'.transform R.adjKernel ⋙ C.transform P) ⋙
        shiftFunctor Y (1 : ℤ) :=
  S.normalizationData.normalizedThird hE

/-- The source-natural counit triangle
`R P ⋙ P ⟶ 𝟙 Y ⟶ twist ⟶ (R P ⋙ P)⟦1⟧`.

Its first map and all three vertices are literal.  Its remaining maps retain
the choices in `S`; this is only an objectwise distinguished family, not a
distinguished triangle in a functor category. -/
noncomputable def counitTriangleInSource : Y ⥤ Triangle Y :=
  S.normalizationData.normalizedTriangle hE

@[simp]
theorem counitTriangleInSource_obj₁ (A : Y) :
    ((S.counitTriangleInSource hE).obj A).obj₁ =
      (C'.transform R.adjKernel ⋙ C.transform P).obj A :=
  rfl

@[simp]
theorem counitTriangleInSource_obj₂ (A : Y) :
    ((S.counitTriangleInSource hE).obj A).obj₂ = A :=
  rfl

@[simp]
theorem counitTriangleInSource_obj₃ (A : Y) :
    ((S.counitTriangleInSource hE).obj A).obj₃ = S.twist.obj A :=
  rfl

@[simp]
theorem counitTriangleInSource_mor₁ (A : Y) :
    ((S.counitTriangleInSource hE).obj A).mor₁ =
      R.adj.counit.app A :=
  rfl

@[simp]
theorem counitTriangleInSource_mor₂ (A : Y) :
    ((S.counitTriangleInSource hE).obj A).mor₂ =
      (S.counitToTwist hE).app A :=
  rfl

@[simp]
theorem counitTriangleInSource_mor₃ (A : Y) :
    ((S.counitTriangleInSource hE).obj A).mor₃ =
      (S.twistToShiftedComposite hE).app A :=
  rfl

/-- The raw exact-family triangle and the literal counit triangle are naturally
isomorphic through the two endpoint comparisons and the identity on the twist
candidate. -/
noncomputable def triangleInSourceIsoCounit :
    S.triangleInSource hE ≅ S.counitTriangleInSource hE :=
  S.normalizationData.rawTriangleIsoNormalized hE

@[simp]
theorem triangleInSourceIsoCounit_hom_app_hom₁ (A : Y) :
    ((S.triangleInSourceIsoCounit hE).hom.app A).hom₁ =
      (S.triangleInSourceObj₁Iso hE).hom.app A :=
  S.normalizationData.rawTriangleIsoNormalized_hom_app_hom₁ hE A

@[simp]
theorem triangleInSourceIsoCounit_hom_app_hom₂ (A : Y) :
    ((S.triangleInSourceIsoCounit hE).hom.app A).hom₂ =
      (S.triangleInSourceObj₂Iso hE).hom.app A :=
  S.normalizationData.rawTriangleIsoNormalized_hom_app_hom₂ hE A

@[simp]
theorem triangleInSourceIsoCounit_hom_app_hom₃ (A : Y) :
    ((S.triangleInSourceIsoCounit hE).hom.app A).hom₃ = 𝟙 _ :=
  S.normalizationData.rawTriangleIsoNormalized_hom_app_hom₃ hE A

/-- Every value of the literal counit triangle is distinguished. -/
theorem counitTriangleInSource_obj_distinguished
    [e.equiv.functor.IsTriangulated] (A : Y) :
    (S.counitTriangleInSource hE).obj A ∈ distTriang Y :=
  S.normalizationData.normalizedTriangle_obj_distinguished hE A

/-- The literal counit-triangle family with codomain restricted to
distinguished triangles. -/
noncomputable def distinguishedCounitTriangleInSource
    [e.equiv.functor.IsTriangulated] :
    Y ⥤ (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
      (Y := Y)).FullSubcategory :=
  S.normalizationData.distinguishedNormalizedTriangle hE

@[simp]
theorem distinguishedCounitTriangleInSource_obj_val
    [e.equiv.functor.IsTriangulated] (A : Y) :
    ((S.distinguishedCounitTriangleInSource hE).obj A).obj =
      (S.counitTriangleInSource hE).obj A :=
  rfl

end Exact

end CounitKernelConeData

namespace KernelTransformationData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : KernelTransformationData E (D.conv R.adjKernel P) U.unitKernel
    (C'.transform R.adjKernel ⋙ C.transform P) (Functor.id Y)
    (D.compIso R.adjKernel P).symm U.unitIso.symm R.adj.counit)

/-- Specialize a generic kernel realization of the adjunction counit to the
stable counit-kernel interface. -/
def toCounitKernelData : CounitKernelData C C' E P R D U where
  arrow := S.arrow
  transform_arrow := S.transform_arrow

@[simp]
theorem toCounitKernelData_toKernelTransformationData :
    S.toCounitKernelData.toKernelTransformationData = S :=
  rfl

end KernelTransformationData

namespace KernelTransformationConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : KernelTransformationConeData E e (D.conv R.adjKernel P) U.unitKernel
    (C'.transform R.adjKernel ⋙ C.transform P) (Functor.id Y)
    (D.compIso R.adjKernel P).symm U.unitIso.symm R.adj.counit)

/-- Specialize a generic enhanced realization of the adjunction counit to the
stable counit-kernel cone interface. -/
def toCounitKernelConeData : CounitKernelConeData C C' E e P R D U where
  arrow := S.arrow
  cone := S.cone
  isCone := S.isCone
  transform_arrow := S.transform_arrow

@[simp]
theorem toCounitKernelConeData_toKernelTransformationConeData :
    S.toCounitKernelConeData.toKernelTransformationConeData = S :=
  rfl

end KernelTransformationConeData

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

@[simp]
theorem toKernelTransformationData_toCounitKernelData :
    S.toKernelTransformationData.toCounitKernelData = S :=
  rfl

end CounitKernelData

namespace CounitKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : CounitKernelConeData C C' E e P R D U)

@[simp]
theorem toKernelTransformationConeData_toCounitKernelConeData :
    S.toKernelTransformationConeData.toCounitKernelConeData = S :=
  rfl

end CounitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
