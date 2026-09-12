/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.CounitKernel

/-!
# Kernel realizations of left-adjunction dual cotwists

Let `Φ_Q ⊣ Φ_P`, where `Φ_P : X ⥤ Y` is a Fourier--Mukai transform
and `Φ_Q : Y ⥤ X` is its supplied kernel-presented left adjoint.  The
adjunction counit is

`Φ_P ⋙ Φ_Q ⟶ id_X`.

Its cone is conventionally the **dual cotwist** of the original functor
`Φ_P`.  This file supplies the semantic left-adjunction API while reusing
`CounitKernelData` and `CounitKernelConeData` with the correspondences swapped
through `LeftAdjointKernelData.toRightAdjointKernelData`.

Thus an ordinary kernel arrow `conv P Q ⟶ O_Δ`, together with its exact
transform equation, has a noncanonically selected enhanced representative and
cone.  Exact kernel evaluation produces the source-natural, pointwise
distinguished family

`Φ_P ⋙ Φ_Q ⟶ id_X ⟶ dualCotwist ⟶ (Φ_P ⋙ Φ_Q)⟦1⟧`.

No new adjunction, cone, normalization, or rotation is constructed here.  The
dual cotwist remains choice-dependent; it is not asserted exact, invertible,
canonical, or spherical.
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

/-- An ordinary kernel arrow realizing the counit of a kernel-presented left
adjunction, named as the dual-cotwist input for the original functor. -/
abbrev DualCotwistKernelData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence X X W) (P : W₁)
    (L : LeftAdjointKernelData C C' P)
    (D : ConvolutionData C C' E) (U : UnitKernelData E) :=
  CounitKernelData C' C E L.adjKernel
    L.toRightAdjointKernelData D U

/-- An enhanced representative and chosen cone for a left-adjunction counit
kernel arrow, named as the dual-cotwist input for the original functor. -/
abbrev DualCotwistKernelConeData
    (C : Correspondence X Y W₁) (C' : Correspondence Y X W₂)
    (E : Correspondence X X W) (e : Enhancement.{vE, uE} W) (P : W₁)
    (L : LeftAdjointKernelData C C' P)
    (D : ConvolutionData C C' E) (U : UnitKernelData E) :=
  CounitKernelConeData C' C E e L.adjKernel
    L.toRightAdjointKernelData D U

namespace DualCotwistKernelData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence X X W} {P : W₁}
  {L : LeftAdjointKernelData C C' P}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}
  (S : DualCotwistKernelData C C' E P L D U)

/-- The specialized transform equation for the left-adjunction counit. -/
theorem transform_arrow :
    E.transformMap S.arrow =
      (D.compIso P L.adjKernel).inv ≫ L.adj.counit ≫ U.unitIso.hom :=
  CounitKernelData.transform_arrow S

/-- Fullness of the kernel transform is sufficient to realize the
left-adjunction counit by an ordinary kernel morphism. -/
noncomputable def ofFull [E.kernelTransform.Full] :
    DualCotwistKernelData C C' E P L D U :=
  CounitKernelData.ofFull

/-- Choose a closed representative and dg cone for the dual-cotwist counit
kernel arrow.  Both choices are noncanonical. -/
noncomputable def toConeData (e : Enhancement.{vE, uE} W) :
    DualCotwistKernelConeData C C' E e P L D U :=
  CounitKernelData.toConeData S e

end DualCotwistKernelData

namespace DualCotwistKernelConeData

variable {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence X X W} {e : Enhancement.{vE, uE} W} {P : W₁}
  {L : LeftAdjointKernelData C C' P}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}
  (S : DualCotwistKernelConeData C C' E e P L D U)

/-- The selected enhanced counit cone read as an ordinary kernel. -/
abbrev dualCotwistKernel : W :=
  CounitKernelConeData.twistKernel S

/-- The transform of the selected cone kernel: the choice-dependent ordinary
dual cotwist. -/
abbrev dualCotwist : X ⥤ X :=
  CounitKernelConeData.twist S

/-- The named dual-cotwist kernel presents the dual cotwist definitionally. -/
def dualCotwistKernelIso : E.transform S.dualCotwistKernel ≅ S.dualCotwist :=
  CounitKernelConeData.twistKernelIso S

/-- The dual cotwist is a kernel functor for the endocorrespondence on `X`.
This does not assert exactness or invertibility. -/
theorem isKernelFunctor_dualCotwist : E.IsKernelFunctor S.dualCotwist :=
  CounitKernelConeData.isKernelFunctor_twist S

/-- The transformed enhanced arrow forms the literal left-adjunction-counit
square. -/
theorem transform_arrow_counit_square :
    E.transformMap (e.equiv.functor.map
        (H0.homMk (C := e.dgCat) S.arrow)) ≫
        (CounitKernelConeData.targetTransformIso S).hom =
      (CounitKernelConeData.sourceTransformIso S).hom ≫ L.adj.counit :=
  CounitKernelConeData.transform_arrow_counit_square S

section Exact

variable [Limits.HasZeroObject X] [HasShift X ℤ] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ] (hE : E.KernelEvaluationExact)

/-- The transported second map from the identity to the dual cotwist. -/
noncomputable def counitToDualCotwist : Functor.id X ⟶ S.dualCotwist :=
  CounitKernelConeData.counitToTwist S hE

/-- The transported connecting map from the dual cotwist to the shifted
left-adjoint composite. -/
noncomputable def dualCotwistToShiftedComposite :
    S.dualCotwist ⟶
      (C.transform P ⋙ C'.transform L.adjKernel) ⋙
        shiftFunctor X (1 : ℤ) :=
  CounitKernelConeData.twistToShiftedComposite S hE

/-- The source-natural dual-cotwist triangle for the original functor
`Φ_P : X ⥤ Y`. -/
noncomputable def dualCotwistTriangleInSource : X ⥤ Triangle X :=
  CounitKernelConeData.counitTriangleInSource S hE

@[simp]
theorem dualCotwistTriangleInSource_obj₁ (A : X) :
    ((S.dualCotwistTriangleInSource hE).obj A).obj₁ =
      (C.transform P ⋙ C'.transform L.adjKernel).obj A :=
  rfl

@[simp]
theorem dualCotwistTriangleInSource_obj₂ (A : X) :
    ((S.dualCotwistTriangleInSource hE).obj A).obj₂ = A :=
  rfl

@[simp]
theorem dualCotwistTriangleInSource_obj₃ (A : X) :
    ((S.dualCotwistTriangleInSource hE).obj A).obj₃ = S.dualCotwist.obj A :=
  rfl

@[simp]
theorem dualCotwistTriangleInSource_mor₁ (A : X) :
    ((S.dualCotwistTriangleInSource hE).obj A).mor₁ = L.adj.counit.app A :=
  rfl

@[simp]
theorem dualCotwistTriangleInSource_mor₂ (A : X) :
    ((S.dualCotwistTriangleInSource hE).obj A).mor₂ =
      (S.counitToDualCotwist hE).app A :=
  rfl

@[simp]
theorem dualCotwistTriangleInSource_mor₃ (A : X) :
    ((S.dualCotwistTriangleInSource hE).obj A).mor₃ =
      (S.dualCotwistToShiftedComposite hE).app A :=
  rfl

/-- At the natural-transformation level, the first map is strictly the
left-adjunction counit. -/
theorem dualCotwistTriangleInSource_counit :
    Functor.whiskerLeft (S.dualCotwistTriangleInSource hE)
        Triangle.π₁Toπ₂ = L.adj.counit :=
  rfl

/-- Every value of the dual-cotwist triangle is distinguished. -/
theorem dualCotwistTriangleInSource_obj_distinguished
    [e.equiv.functor.IsTriangulated] (A : X) :
    (S.dualCotwistTriangleInSource hE).obj A ∈ distTriang X :=
  CounitKernelConeData.counitTriangleInSource_obj_distinguished S hE A

/-- The dual-cotwist triangle family valued in distinguished triangles. -/
noncomputable def distinguishedDualCotwistTriangleInSource
    [e.equiv.functor.IsTriangulated] :
    X ⥤ (Correspondence.KernelEvaluationExact.pointwiseDistinguishedTriangleProperty
      (Y := X)).FullSubcategory :=
  CounitKernelConeData.distinguishedCounitTriangleInSource S hE

@[simp]
theorem distinguishedDualCotwistTriangleInSource_obj_val
    [e.equiv.functor.IsTriangulated] (A : X) :
    ((S.distinguishedDualCotwistTriangleInSource hE).obj A).obj =
      (S.dualCotwistTriangleInSource hE).obj A :=
  rfl

end Exact

end DualCotwistKernelConeData

end CategoryTheory.Triangulated.FourierMukai
