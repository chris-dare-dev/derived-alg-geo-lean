/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Rotate
import DerivedAlgGeo.CategoryTheory.Shift.FunctorCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Autoequivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.KernelTransformation

/-!
# Kernel realizations of adjunction units

Let `Φ_P : X ⥤ Y` have a kernel-presented right adjoint `Φ_Q`.  With a
convolution kernel and a diagonal unit kernel on `X`, the adjunction unit has
the form

`Φ_{O_Δ} ⟶ Φ_{conv P Q}`.

Here `conv P Q` presents `Φ_P ⋙ Φ_Q`.  The abbreviations
`AdjunctionUnitKernelData` and `AdjunctionUnitKernelConeData` specialize the
generic kernel-transformation interfaces to an ordinary kernel morphism
`O_Δ ⟶ conv P Q`, its enhanced representative, and a chosen dg cone.  They
are abbreviations rather than parallel records, since there is no legacy unit
realization API to preserve.

Exactness in the kernel variable gives a source-natural, pointwise
distinguished unshifted unit triangle

`𝟭 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwistCone ⟶ (𝟭 X)⟦1⟧`.

The third functor is the unshifted cotwist-cone candidate.  Its pointwise
`[-1]` shift is the conventional, choice-dependent ordinary cotwist, and
inverse rotation gives the source-natural triangle

`cotwist ⟶ 𝟭 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwist⟦1⟧`.

The shift and inverse rotation reuse the functor-category `HasShift` instance
and Mathlib's `invRotate`; no signed map is reconstructed here.  The existing
shift comparison of a shift-coherent kernel family presents the cotwist by the
cone kernel shifted inside the enhancement's homotopy category.  No
representative or cone is canonical, and no exactness, autoequivalence, or
sphericality claim is made.

`AdjunctionUnitKernelData.ofFull` is only a sufficient abstract constructor.
Without the explicit fullness hypothesis, producing the kernel arrow remains
the geometric unit-realization obligation.
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

/-- An ordinary kernel arrow realizing the unit of a kernel-presented right
adjunction.  This is a definitional specialization of the generic
kernel-transformation interface. -/
abbrev AdjunctionUnitKernelData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence X X W) (P : W₁)
    (R : RightAdjointKernelData C C' P)
    (D : ConvolutionData C C' E) (U : UnitKernelData E) :=
  KernelTransformationData E U.unitKernel (D.conv P R.adjKernel)
    (Functor.id X) (C.transform P ⋙ C'.transform R.adjKernel)
    U.unitIso.symm (D.compIso P R.adjKernel).symm R.adj.unit

/-- An enhanced representative and chosen dg cone of a kernel arrow realizing
the unit of a kernel-presented right adjunction. -/
abbrev AdjunctionUnitKernelConeData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence X X W) (e : Enhancement.{vE, uE} W) (P : W₁)
    (R : RightAdjointKernelData C C' P)
    (D : ConvolutionData C C' E) (U : UnitKernelData E) :=
  KernelTransformationConeData E e U.unitKernel (D.conv P R.adjKernel)
    (Functor.id X) (C.transform P ⋙ C'.transform R.adjKernel)
    U.unitIso.symm (D.compIso P R.adjKernel).symm R.adj.unit

namespace AdjunctionUnitKernelData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence X X W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}
  (S : AdjunctionUnitKernelData C C' E P R D U)

/-- The specialized kernel-transform equation for the adjunction unit. -/
theorem transform_arrow :
    E.transformMap S.arrow =
      U.unitIso.inv ≫ R.adj.unit ≫ (D.compIso P R.adjKernel).hom :=
  KernelTransformationData.transform_arrow S

/-- Fullness of the kernel transform is sufficient to realize the adjunction
unit by an ordinary kernel morphism. -/
noncomputable def ofFull [E.kernelTransform.Full] :
    AdjunctionUnitKernelData C C' E P R D U :=
  KernelTransformationData.ofFull

/-- Choose a closed representative and dg cone for the unit-kernel arrow.
Both choices are noncanonical. -/
noncomputable def toConeData (e : Enhancement.{vE, uE} W) :
    AdjunctionUnitKernelConeData C C' E e P R D U :=
  KernelTransformationData.toConeData S e

end AdjunctionUnitKernelData

namespace AdjunctionUnitKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence X X W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {R : RightAdjointKernelData C C' P}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}
  (S : AdjunctionUnitKernelConeData C C' E e P R D U)

/-- The transform of the selected cone: the unshifted cotwist-cone
candidate. -/
abbrev cotwistCone : X ⥤ X :=
  (KernelTransformationConeData.normalizationData S).coneTransform

section Shift

variable [HasShift X ℤ]

/-- The conventional, choice-dependent ordinary cotwist: the pointwise
`[-1]` shift of the selected cotwist-cone transform.  This is a functor only;
no exactness or equivalence is asserted. -/
noncomputable abbrev cotwist : X ⥤ X :=
  (shiftFunctor (X ⥤ X) (-1 : ℤ)).obj S.cotwistCone

section Kernel

variable [HasShift W ℤ] [e.equiv.functor.CommShift ℤ]

/-- The selected kernel presenting the conventional cotwist: shift the
enhanced unit cone by `-1` before transporting it to the ordinary kernel
category. -/
noncomputable abbrev cotwistKernel : W :=
  S.normalizationData.shiftedConeKernel (-1 : ℤ)

/-- The kernel family's shift comparison identifies the transform of
`cotwistKernel` with the pointwise shifted cotwist-cone functor. -/
noncomputable def cotwistKernelIso
    (hShift : E.kernelTransform.CommShift ℤ) :
    E.transform S.cotwistKernel ≅ S.cotwist :=
  S.normalizationData.shiftedConeTransformIso hShift (-1 : ℤ)

/-- The conventional cotwist is a Fourier--Mukai kernel functor, presented by
the explicitly named shifted cone kernel.  This asserts neither exactness nor
invertibility of the cotwist. -/
theorem isKernelFunctor_cotwist
    (hShift : E.kernelTransform.CommShift ℤ) :
    E.IsKernelFunctor S.cotwist :=
  ⟨S.cotwistKernel, ⟨(S.cotwistKernelIso hShift).symm⟩⟩

end Kernel

end Shift

/-- The transformed enhanced arrow forms the literal adjunction-unit square. -/
theorem transform_arrow_unit_square :
    E.transformMap (e.equiv.functor.map
        (H0.homMk (C := e.dgCat) S.arrow)) ≫
        (KernelTransformationConeData.targetTransformIso S).hom =
      (KernelTransformationConeData.sourceTransformIso S).hom ≫ R.adj.unit :=
  KernelTransformationConeData.transform_arrow_square S

section Exact

variable [Limits.HasZeroObject X] [HasShift X ℤ] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ] (hE : E.KernelEvaluationExact)

/-- The transported second map from `Φ_P ⋙ Φ_Q` to the unshifted cotwist-cone
candidate. -/
noncomputable def compositeToCotwistCone :
    C.transform P ⋙ C'.transform R.adjKernel ⟶ S.cotwistCone :=
  S.normalizationData.normalizedSecond hE

/-- The transported connecting map from the unshifted cotwist-cone candidate
to the shifted identity functor. -/
noncomputable def cotwistConeToShiftedIdentity :
    S.cotwistCone ⟶ Functor.id X ⋙ shiftFunctor X (1 : ℤ) :=
  S.normalizationData.normalizedThird hE

/-- The source-natural unshifted unit triangle
`𝟙 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwistCone ⟶ (𝟙 X)⟦1⟧`.

Its first map and all three vertices are literal.  It is only an objectwise
distinguished family, not a distinguished triangle in a functor category. -/
noncomputable def unitTriangleInSource : X ⥤ Triangle X :=
  S.normalizationData.normalizedTriangle hE

@[simp]
theorem unitTriangleInSource_obj₁ (A : X) :
    ((S.unitTriangleInSource hE).obj A).obj₁ = A :=
  rfl

@[simp]
theorem unitTriangleInSource_obj₂ (A : X) :
    ((S.unitTriangleInSource hE).obj A).obj₂ =
      (C.transform P ⋙ C'.transform R.adjKernel).obj A :=
  rfl

@[simp]
theorem unitTriangleInSource_obj₃ (A : X) :
    ((S.unitTriangleInSource hE).obj A).obj₃ = S.cotwistCone.obj A :=
  rfl

@[simp]
theorem unitTriangleInSource_mor₁ (A : X) :
    ((S.unitTriangleInSource hE).obj A).mor₁ = R.adj.unit.app A :=
  rfl

@[simp]
theorem unitTriangleInSource_mor₂ (A : X) :
    ((S.unitTriangleInSource hE).obj A).mor₂ =
      (S.compositeToCotwistCone hE).app A :=
  rfl

@[simp]
theorem unitTriangleInSource_mor₃ (A : X) :
    ((S.unitTriangleInSource hE).obj A).mor₃ =
      (S.cotwistConeToShiftedIdentity hE).app A :=
  rfl

/-- Every value of the literal unshifted unit triangle is distinguished. -/
theorem unitTriangleInSource_obj_distinguished
    [e.equiv.functor.IsTriangulated] (A : X) :
    (S.unitTriangleInSource hE).obj A ∈ distTriang X :=
  S.normalizationData.normalizedTriangle_obj_distinguished hE A

/-- The literal unshifted unit-triangle family with codomain restricted to
distinguished triangles. -/
noncomputable def distinguishedUnitTriangleInSource
    [e.equiv.functor.IsTriangulated] :
    X ⥤ (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
      (Y := X)).FullSubcategory :=
  S.normalizationData.distinguishedNormalizedTriangle hE

@[simp]
theorem distinguishedUnitTriangleInSource_obj_val
    [e.equiv.functor.IsTriangulated] (A : X) :
    ((S.distinguishedUnitTriangleInSource hE).obj A).obj =
      (S.unitTriangleInSource hE).obj A :=
  rfl

/-! ### The conventional cotwist triangle -/

/-- The inverse rotation of the unshifted unit triangle:
`cotwist ⟶ 𝟭 X ⟶ Φ_P ⋙ Φ_Q ⟶ cotwist⟦1⟧`.

Mathlib's inverse rotation owns the minus sign in the first map. -/
noncomputable def cotwistTriangleInSource : X ⥤ Triangle X :=
  S.unitTriangleInSource hE ⋙ invRotate X

/-- The first projection of the rotated triangle is strictly the pointwise
shifted cotwist-cone functor. -/
theorem cotwistTriangleInSource_comp_π₁ :
    S.cotwistTriangleInSource hE ⋙ Triangle.π₁ = S.cotwist :=
  rfl

/-- The second projection of the rotated triangle is strictly the identity. -/
theorem cotwistTriangleInSource_comp_π₂ :
    S.cotwistTriangleInSource hE ⋙ Triangle.π₂ = Functor.id X :=
  rfl

/-- The third projection of the rotated triangle is strictly the composite
adjoint transform. -/
theorem cotwistTriangleInSource_comp_π₃ :
    S.cotwistTriangleInSource hE ⋙ Triangle.π₃ =
      C.transform P ⋙ C'.transform R.adjKernel :=
  rfl

@[simp]
theorem cotwistTriangleInSource_obj₁ (A : X) :
    ((S.cotwistTriangleInSource hE).obj A).obj₁ = S.cotwist.obj A :=
  rfl

@[simp]
theorem cotwistTriangleInSource_obj₂ (A : X) :
    ((S.cotwistTriangleInSource hE).obj A).obj₂ = A :=
  rfl

@[simp]
theorem cotwistTriangleInSource_obj₃ (A : X) :
    ((S.cotwistTriangleInSource hE).obj A).obj₃ =
      (C.transform P ⋙ C'.transform R.adjKernel).obj A :=
  rfl

/-- At the natural-transformation level, the second map is strictly the
adjunction unit. -/
theorem cotwistTriangleInSource_unit :
    Functor.whiskerLeft (S.cotwistTriangleInSource hE)
        Triangle.π₂Toπ₃ = R.adj.unit :=
  rfl

/-- Inverse rotation moves the adjunction unit into the second map. -/
@[simp]
theorem cotwistTriangleInSource_mor₂ (A : X) :
    ((S.cotwistTriangleInSource hE).obj A).mor₂ = R.adj.unit.app A :=
  congr_app (S.cotwistTriangleInSource_unit hE) A

/-- Every value of the conventional cotwist triangle is distinguished. -/
theorem cotwistTriangleInSource_obj_distinguished
    [e.equiv.functor.IsTriangulated] (A : X) :
    (S.cotwistTriangleInSource hE).obj A ∈ distTriang X :=
  inv_rot_of_distTriang _ (S.unitTriangleInSource_obj_distinguished hE A)

/-- The conventional cotwist-triangle family with codomain restricted to
distinguished triangles. -/
noncomputable def distinguishedCotwistTriangleInSource
    [e.equiv.functor.IsTriangulated] :
    X ⥤ (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
      (Y := X)).FullSubcategory :=
  (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
    (Y := X)).lift (S.cotwistTriangleInSource hE)
      (S.cotwistTriangleInSource_obj_distinguished hE)

@[simp]
theorem distinguishedCotwistTriangleInSource_obj_val
    [e.equiv.functor.IsTriangulated] (A : X) :
    ((S.distinguishedCotwistTriangleInSource hE).obj A).obj =
      (S.cotwistTriangleInSource hE).obj A :=
  rfl

end Exact

end AdjunctionUnitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
