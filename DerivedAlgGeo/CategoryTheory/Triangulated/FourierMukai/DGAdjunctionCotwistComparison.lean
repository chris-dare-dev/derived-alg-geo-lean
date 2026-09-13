/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCotwistPresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.AdjunctionUnitKernel
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionPresentation

/-!
# Comparing presented dg and Fourier--Mukai cotwists

Suppose a strict dg adjunction is presented on ordinary categories by a pair
of Fourier--Mukai transforms.  A chosen dg cone on its unit and an independently
chosen enhanced Fourier--Mukai cone then give two pointwise distinguished unit
triangles with the same first two vertices and the same first map.

Mathlib's `isoTriangleOfIso₁₂` therefore supplies a noncanonical
isomorphism between the two triangles at each source object.  Applying
`invRotate` gives the corresponding comparison between the conventional
cotwist triangles, with Mathlib retaining ownership of the sign and shift
cancellation.  The first component compares the transported dg cotwist object
with the Fourier--Mukai cotwist object.

The completion chosen by `isoTriangleOfIso₁₂` is made separately at each
object.  Nothing here proves that these comparisons are natural in the source
object, independent of either cone choice, exact, or compatible with the
chosen `CommShift` structures.  In particular, this file constructs no
functor isomorphism and transfers no equivalence, kernel-presentation, or
sphericality statement.
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
  {E : Correspondence X X W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}

namespace AdjunctionUnitKernelConeData

variable [IsPretriangulated A]
  [Limits.HasZeroObject X] [HasShift X ℤ] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eA.functor.CommShift ℤ] [eA.functor.IsTriangulated]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ] [e.equiv.functor.IsTriangulated]
  (adj : DGAdjunction L R)
  (H : DGAdjunction.H0Presentation (L := L) (R := R) eA eB
    (C.transform P) (C'.transform Q))
  (K : adj.UnitConeData)
  (S : AdjunctionUnitKernelConeData C C' E e P
    (RightAdjointKernelData.ofH0Presentation H adj) D U)
  (hE : E.KernelEvaluationExact)

/-- At each object, the presented dg unit triangle is noncanonically
isomorphic to the independently chosen Fourier--Mukai unit triangle.

The isomorphism is the identity on the identity and adjunction-composite
vertices.  Its third component is the choice made by triangulated-category
completion and is not asserted to be natural in `Z`. -/
noncomputable def presentedUnitTriangleObjIso (Z : X) :
    (H.presentedUnitTriangle K).obj Z ≅
      (S.unitTriangleInSource hE).obj Z := by
  refine isoTriangleOfIso₁₂ _ _
    (H.presentedUnitTriangle_obj_distinguished K Z)
    (S.unitTriangleInSource_obj_distinguished hE Z)
    (Iso.refl _) (Iso.refl _) ?_
  simp [RightAdjointKernelData.ofH0Presentation_adj]

/-- The first component of the unit-triangle comparison is the identity. -/
@[simp]
theorem presentedUnitTriangleObjIso_hom_hom₁ (Z : X) :
    ((S.presentedUnitTriangleObjIso adj H K hE Z).hom).hom₁ = 𝟙 Z := by
  simp [presentedUnitTriangleObjIso]

/-- The second component of the unit-triangle comparison is the identity. -/
@[simp]
theorem presentedUnitTriangleObjIso_hom_hom₂ (Z : X) :
    ((S.presentedUnitTriangleObjIso adj H K hE Z).hom).hom₂ =
      𝟙 ((C.transform P ⋙ C'.transform Q).obj Z) := by
  simp [presentedUnitTriangleObjIso]

/-- The resulting noncanonical objectwise comparison between the transported
dg unit cone and the Fourier--Mukai unit cone. -/
noncomputable def transportedUnitConeObjIso (Z : X) :
    (K.transportedUnitCone eA).obj Z ≅ S.cotwistCone.obj Z :=
  Triangle.π₃.mapIso (S.presentedUnitTriangleObjIso adj H K hE Z)

/-- Inverse rotation of the unit-triangle comparison gives a noncanonical
objectwise comparison of the conventional cotwist triangles. -/
noncomputable def presentedCotwistTriangleObjIso (Z : X) :
    (H.presentedCotwistTriangle K).obj Z ≅
      (S.cotwistTriangleInSource hE).obj Z :=
  (invRotate X).mapIso (S.presentedUnitTriangleObjIso adj H K hE Z)

/-- The second component of the cotwist-triangle comparison is the identity. -/
@[simp]
theorem presentedCotwistTriangleObjIso_hom_hom₂ (Z : X) :
    ((S.presentedCotwistTriangleObjIso adj H K hE Z).hom).hom₂ = 𝟙 Z := by
  simp [presentedCotwistTriangleObjIso]

/-- The third component of the cotwist-triangle comparison is the identity. -/
@[simp]
theorem presentedCotwistTriangleObjIso_hom_hom₃ (Z : X) :
    ((S.presentedCotwistTriangleObjIso adj H K hE Z).hom).hom₃ =
      𝟙 ((C.transform P ⋙ C'.transform Q).obj Z) := by
  simp [presentedCotwistTriangleObjIso]

/-- The resulting noncanonical objectwise comparison between the transported
dg cotwist and the Fourier--Mukai cotwist. -/
noncomputable def transportedCotwistObjIso (Z : X) :
    (K.transportedCotwist eA).obj Z ≅ S.cotwist.obj Z :=
  Triangle.π₁.mapIso (S.presentedCotwistTriangleObjIso adj H K hE Z)

/-- The actual shifted dg cone, after `H⁰` and ordinary transport, is
noncanonically objectwise isomorphic to the Fourier--Mukai cotwist. -/
noncomputable def transportedDGCotwistObjIso (Z : X) :
    (K.transportedDGCotwist eA).obj Z ≅ S.cotwist.obj Z :=
  (K.transportedCotwistH0Iso (eC := eA)).app Z ≪≫
    S.transportedCotwistObjIso adj H K hE Z

end AdjunctionUnitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
