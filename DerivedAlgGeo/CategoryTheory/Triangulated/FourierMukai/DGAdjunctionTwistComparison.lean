/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionConePresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.CounitKernel
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionPresentation

/-!
# Comparing presented dg and Fourier--Mukai twists

Suppose a strict dg adjunction is presented on ordinary categories by a pair
of Fourier--Mukai transforms.  A chosen dg cone on its counit and an
independently chosen enhanced Fourier--Mukai cone then give two pointwise
distinguished counit triangles with the same first two vertices and the same
first map.

Mathlib's `isoTriangleOfIso₁₂` supplies a noncanonical isomorphism between
the two triangles at each target object.  Its third component compares the
ordinary transport of the actual dg twist with the Fourier--Mukai twist.

The completion is chosen separately at each object.  Nothing here proves that
these comparisons are natural in the target object, independent of either
cone choice, exact, or compatible with chosen `CommShift` structures.  In
particular, this file constructs no functor isomorphism and transfers no
equivalence, kernel-presentation, or sphericality statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY v₁ v₂ vW vE uA uB uX uY u₁ u₂ uW uE

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W₁ : Type u₁} {W₂ : Type u₂} {W : Type uW}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{v₁} W₁] [Category.{v₂} W₂] [Category.{vW} W]
  {L : DGFunctor A B} {R : DGFunctor B A}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}

namespace CounitKernelConeData

variable [IsPretriangulated B]
  [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [eB.functor.CommShift ℤ] [eB.functor.IsTriangulated]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ] [e.equiv.functor.IsTriangulated]
  (adj : DGAdjunction L R)
  (H : DGAdjunction.H0Presentation (L := L) (R := R) eA eB
    (C.transform P) (C'.transform Q))
  (K : adj.CounitConeData)
  (S : CounitKernelConeData C C' E e P
    (RightAdjointKernelData.ofH0Presentation H adj) D U)
  (hE : E.KernelEvaluationExact)

/-- At each target object, the presented dg counit triangle is noncanonically
isomorphic to the independently chosen Fourier--Mukai counit triangle.

The isomorphism is the identity on the adjunction-composite and identity
vertices.  Its third component is the choice made by triangulated-category
completion and is not asserted to be natural in `Z`. -/
noncomputable def presentedCounitTriangleObjIso (Z : Y) :
    (H.presentedCounitTriangle K).obj Z ≅
      (S.counitTriangleInSource hE).obj Z := by
  refine isoTriangleOfIso₁₂ _ _
    (H.presentedCounitTriangle_obj_distinguished K Z)
    (S.counitTriangleInSource_obj_distinguished hE Z)
    (Iso.refl _) (Iso.refl _) ?_
  simp [RightAdjointKernelData.ofH0Presentation_adj]

/-- The first component of the counit-triangle comparison is the identity. -/
@[simp]
theorem presentedCounitTriangleObjIso_hom_hom₁ (Z : Y) :
    ((S.presentedCounitTriangleObjIso adj H K hE Z).hom).hom₁ =
      𝟙 ((C'.transform Q ⋙ C.transform P).obj Z) := by
  simp [presentedCounitTriangleObjIso]

/-- The second component of the counit-triangle comparison is the identity. -/
@[simp]
theorem presentedCounitTriangleObjIso_hom_hom₂ (Z : Y) :
    ((S.presentedCounitTriangleObjIso adj H K hE Z).hom).hom₂ = 𝟙 Z := by
  simp [presentedCounitTriangleObjIso]

/-- The resulting noncanonical objectwise comparison between the transported
actual dg twist and the Fourier--Mukai twist. -/
noncomputable def transportedTwistObjIso (Z : Y) :
    (K.transportedTwist eB).obj Z ≅ S.twist.obj Z :=
  Triangle.π₃.mapIso (S.presentedCounitTriangleObjIso adj H K hE Z)

end CounitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
