/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.AdjunctionUnitKernel

/-!
# Kernel realizations of left-adjunction dual twists

Let `Φ_Q ⊣ Φ_P`, where `Φ_P : X ⥤ Y` is presented by a kernel for a
correspondence `C` and `Φ_Q : Y ⥤ X` is its supplied kernel-presented left
adjoint.  The adjunction unit has the form

`id_Y ⟶ Φ_Q ⋙ Φ_P`.

For the original functor `Φ_P`, the inverse rotation of the unit-cone
triangle is conventionally called the **dual twist** triangle

`dualTwist ⟶ id_Y ⟶ Φ_Q ⋙ Φ_P ⟶ dualTwist⟦1⟧`.

The implementation introduces no second cone or normalization mechanism.
`LeftAdjointKernelData.toRightAdjointKernelData` reads the same adjunction as a
right adjunction for `Φ_Q`, and all constructions below delegate to the
right-adjunction unit/cotwist interface with the two correspondences swapped.
The public names here retain the dual-twist convention of the original
functor.

The ordinary unit-kernel arrow, its enhanced representative, and its cone are
still supplied or selected noncanonically.  Nothing here makes the dual twist
exact, invertible, canonical, or spherical, and no dual-cotwist construction
is bundled into this lane.
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

/-- An ordinary kernel arrow realizing the unit of a kernel-presented left
adjunction, named as the dual-twist input for the original functor. -/
abbrev DualTwistKernelData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence Y Y W) (P : W₁)
    (L : LeftAdjointKernelData C C' P)
    (D : ConvolutionData C' C E) (U : UnitKernelData E) :=
  AdjunctionUnitKernelData C' C E L.adjKernel
    L.toRightAdjointKernelData D U

/-- An enhanced representative and chosen cone for a left-adjunction unit
kernel arrow, named as the dual-twist input for the original functor. -/
abbrev DualTwistKernelConeData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence Y Y W) (e : Enhancement.{vE, uE} W) (P : W₁)
    (L : LeftAdjointKernelData C C' P)
    (D : ConvolutionData C' C E) (U : UnitKernelData E) :=
  AdjunctionUnitKernelConeData C' C E e L.adjKernel
    L.toRightAdjointKernelData D U

namespace DualTwistKernelData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁}
  {L : LeftAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : DualTwistKernelData C C' E P L D U)

/-- The specialized transform equation for the left-adjunction unit. -/
theorem transform_arrow :
    E.transformMap S.arrow =
      U.unitIso.inv ≫ L.adj.unit ≫ (D.compIso L.adjKernel P).hom :=
  AdjunctionUnitKernelData.transform_arrow S

/-- Fullness of the kernel transform is sufficient to realize the
left-adjunction unit by an ordinary kernel morphism. -/
noncomputable def ofFull [E.kernelTransform.Full] :
    DualTwistKernelData C C' E P L D U :=
  AdjunctionUnitKernelData.ofFull

/-- Choose a closed representative and dg cone for the dual-twist unit-kernel
arrow.  Both choices are noncanonical. -/
noncomputable def toConeData (e : Enhancement.{vE, uE} W) :
    DualTwistKernelConeData C C' E e P L D U :=
  AdjunctionUnitKernelData.toConeData S e

end DualTwistKernelData

namespace DualTwistKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {L : LeftAdjointKernelData C C' P}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  (S : DualTwistKernelConeData C C' E e P L D U)

/-- The unshifted cone of the left-adjunction unit. -/
abbrev dualTwistCone : Y ⥤ Y :=
  AdjunctionUnitKernelConeData.cotwistCone S

section Shift

variable [HasShift Y ℤ]

/-- The choice-dependent ordinary dual twist: the pointwise `[-1]` shift of
the selected left-unit cone transform. -/
noncomputable abbrev dualTwist : Y ⥤ Y :=
  AdjunctionUnitKernelConeData.cotwist S

section Kernel

variable [HasShift W ℤ] [e.equiv.functor.CommShift ℤ]

/-- The shifted enhanced cone kernel presenting the dual twist. -/
noncomputable abbrev dualTwistKernel : W :=
  AdjunctionUnitKernelConeData.cotwistKernel S

/-- The transform of `dualTwistKernel` is the dual twist. -/
noncomputable def dualTwistKernelIso
    (hShift : E.kernelTransform.CommShift ℤ) :
    E.transform S.dualTwistKernel ≅ S.dualTwist :=
  AdjunctionUnitKernelConeData.cotwistKernelIso S hShift

/-- The dual twist is a kernel functor for the endocorrespondence on `Y`.
This does not assert exactness or invertibility. -/
theorem isKernelFunctor_dualTwist
    (hShift : E.kernelTransform.CommShift ℤ) :
    E.IsKernelFunctor S.dualTwist :=
  AdjunctionUnitKernelConeData.isKernelFunctor_cotwist S hShift

end Kernel

end Shift

/-- The transformed enhanced arrow forms the literal left-adjunction-unit
square. -/
theorem transform_arrow_unit_square :
    E.transformMap (e.equiv.functor.map
        (H0.homMk (C := e.dgCat) S.arrow)) ≫
        (KernelTransformationConeData.targetTransformIso S).hom =
      (KernelTransformationConeData.sourceTransformIso S).hom ≫ L.adj.unit :=
  AdjunctionUnitKernelConeData.transform_arrow_unit_square S

section Exact

variable [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ] (hE : E.KernelEvaluationExact)

/-- The transported second map from `Φ_Q ⋙ Φ_P` to the unshifted
dual-twist cone. -/
noncomputable def compositeToDualTwistCone :
    C'.transform L.adjKernel ⋙ C.transform P ⟶ S.dualTwistCone :=
  AdjunctionUnitKernelConeData.compositeToCotwistCone S hE

/-- The transported connecting map from the unshifted dual-twist cone to the
shifted identity. -/
noncomputable def dualTwistConeToShiftedIdentity :
    S.dualTwistCone ⟶ Functor.id Y ⋙ shiftFunctor Y (1 : ℤ) :=
  AdjunctionUnitKernelConeData.cotwistConeToShiftedIdentity S hE

/-- The source-natural unshifted left-unit triangle on the target `Y` of the
original functor `Φ_P`. -/
noncomputable def unitTriangleInTarget : Y ⥤ Triangle Y :=
  AdjunctionUnitKernelConeData.unitTriangleInSource S hE

@[simp]
theorem unitTriangleInTarget_obj₁ (A : Y) :
    ((S.unitTriangleInTarget hE).obj A).obj₁ = A :=
  rfl

@[simp]
theorem unitTriangleInTarget_obj₂ (A : Y) :
    ((S.unitTriangleInTarget hE).obj A).obj₂ =
      (C'.transform L.adjKernel ⋙ C.transform P).obj A :=
  rfl

@[simp]
theorem unitTriangleInTarget_obj₃ (A : Y) :
    ((S.unitTriangleInTarget hE).obj A).obj₃ = S.dualTwistCone.obj A :=
  rfl

@[simp]
theorem unitTriangleInTarget_mor₁ (A : Y) :
    ((S.unitTriangleInTarget hE).obj A).mor₁ = L.adj.unit.app A :=
  rfl

@[simp]
theorem unitTriangleInTarget_mor₂ (A : Y) :
    ((S.unitTriangleInTarget hE).obj A).mor₂ =
      (S.compositeToDualTwistCone hE).app A :=
  rfl

@[simp]
theorem unitTriangleInTarget_mor₃ (A : Y) :
    ((S.unitTriangleInTarget hE).obj A).mor₃ =
      (S.dualTwistConeToShiftedIdentity hE).app A :=
  rfl

/-- Every value of the left-adjunction unit triangle is distinguished. -/
theorem unitTriangleInTarget_obj_distinguished
    [e.equiv.functor.IsTriangulated] (A : Y) :
    (S.unitTriangleInTarget hE).obj A ∈ distTriang Y :=
  AdjunctionUnitKernelConeData.unitTriangleInSource_obj_distinguished S hE A

/-- The left-unit triangle family valued in distinguished triangles. -/
noncomputable def distinguishedUnitTriangleInTarget
    [e.equiv.functor.IsTriangulated] :
    Y ⥤ (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
      (Y := Y)).FullSubcategory :=
  AdjunctionUnitKernelConeData.distinguishedUnitTriangleInSource S hE

@[simp]
theorem distinguishedUnitTriangleInTarget_obj_val
    [e.equiv.functor.IsTriangulated] (A : Y) :
    ((S.distinguishedUnitTriangleInTarget hE).obj A).obj =
      (S.unitTriangleInTarget hE).obj A :=
  rfl

/-- The conventional dual-twist triangle, obtained by inverse rotation of the
left-adjunction unit triangle. -/
noncomputable def dualTwistTriangleInTarget : Y ⥤ Triangle Y :=
  AdjunctionUnitKernelConeData.cotwistTriangleInSource S hE

/-- The first projection of the dual-twist triangle is strictly the dual
twist. -/
theorem dualTwistTriangleInTarget_comp_π₁ :
    S.dualTwistTriangleInTarget hE ⋙ Triangle.π₁ = S.dualTwist :=
  rfl

/-- The second projection is strictly the identity. -/
theorem dualTwistTriangleInTarget_comp_π₂ :
    S.dualTwistTriangleInTarget hE ⋙ Triangle.π₂ = Functor.id Y :=
  rfl

/-- The third projection is strictly the left-adjoint composite. -/
theorem dualTwistTriangleInTarget_comp_π₃ :
    S.dualTwistTriangleInTarget hE ⋙ Triangle.π₃ =
      C'.transform L.adjKernel ⋙ C.transform P :=
  rfl

@[simp]
theorem dualTwistTriangleInTarget_obj₁ (A : Y) :
    ((S.dualTwistTriangleInTarget hE).obj A).obj₁ = S.dualTwist.obj A :=
  rfl

@[simp]
theorem dualTwistTriangleInTarget_obj₂ (A : Y) :
    ((S.dualTwistTriangleInTarget hE).obj A).obj₂ = A :=
  rfl

@[simp]
theorem dualTwistTriangleInTarget_obj₃ (A : Y) :
    ((S.dualTwistTriangleInTarget hE).obj A).obj₃ =
      (C'.transform L.adjKernel ⋙ C.transform P).obj A :=
  rfl

/-- At the natural-transformation level, the second map is strictly the
left-adjunction unit. -/
theorem dualTwistTriangleInTarget_unit :
    Functor.whiskerLeft (S.dualTwistTriangleInTarget hE)
        Triangle.π₂Toπ₃ = L.adj.unit :=
  rfl

@[simp]
theorem dualTwistTriangleInTarget_mor₂ (A : Y) :
    ((S.dualTwistTriangleInTarget hE).obj A).mor₂ = L.adj.unit.app A :=
  congr_app (S.dualTwistTriangleInTarget_unit hE) A

/-- Every value of the dual-twist triangle is distinguished. -/
theorem dualTwistTriangleInTarget_obj_distinguished
    [e.equiv.functor.IsTriangulated] (A : Y) :
    (S.dualTwistTriangleInTarget hE).obj A ∈ distTriang Y :=
  AdjunctionUnitKernelConeData.cotwistTriangleInSource_obj_distinguished S hE A

/-- The dual-twist triangle family valued in distinguished triangles. -/
noncomputable def distinguishedDualTwistTriangleInTarget
    [e.equiv.functor.IsTriangulated] :
    Y ⥤ (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
      (Y := Y)).FullSubcategory :=
  AdjunctionUnitKernelConeData.distinguishedCotwistTriangleInSource S hE

@[simp]
theorem distinguishedDualTwistTriangleInTarget_obj_val
    [e.equiv.functor.IsTriangulated] (A : Y) :
    ((S.distinguishedDualTwistTriangleInTarget hE).obj A).obj =
      (S.dualTwistTriangleInTarget hE).obj A :=
  rfl

end Exact

end DualTwistKernelConeData

end CategoryTheory.Triangulated.FourierMukai
