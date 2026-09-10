/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.AdjunctionH0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationCone

/-!
# The twist triangle of a dg adjunction

For a dg adjunction `L ⊣ R` the counit is a closed degree-zero dg natural
transformation `L R ⟶ id_D`, and a choice of objectwise cones for it is
`CounitConeData`, whose cone functor is the twist candidate.  Feeding that
choice to `ConeData.triangleFunctor` gives

`H⁰ D ⥤ Triangle (H⁰ D)`,   `X ↦ (L R X ⟶ X ⟶ T X ⟶ (L R X)⟦1⟧)`,

every value distinguished.  This is Anno--Logvinenko's twist triangle read as
a triangle of functors on `H⁰` rather than object by object.

The unit side is the same construction in `C`, and its cone is the *unshifted*
cone of `id_C ⟶ R L`; the conventional cotwist is a shift of it, which this
file does not take.

## What is claimed, and what is not

The only claims here are that the triangle is functorial, that every value is
distinguished, and that the construction does not depend on the chosen cones
(`twistTriangleIso`).  All three are immediate from the generic cone-triangle
layer; nothing about adjunctions is used beyond the counit being closed.

Nothing here says the twist is an autoequivalence, calls the adjunction
spherical, or relates the triangle to the other three of Anno--Logvinenko's
four.  Those need the Morita and quasi-functor framework the roadmap lists as
open, and the repository's dg adjunctions are the strict kind, not homotopy
adjunctions of bimodules.

## Where the first two maps come from

`twistTriangleFunctor_obj_mor₁` identifies the first map with the counit read
on `H⁰`, which is `DGAdjunction.h0Counit`, and `..._mor₂` identifies the
second with the canonical inclusion `id_D ⟶ T`.  Both are the point of the
construction: the triangle's maps are the adjunction's own data, not new
choices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace DGAdjunction

variable {C : Type u} {D : Type u'}
  [DGCategory.{v} C] [DGCategory.{v} D]
  {L : DGFunctor C D} {R : DGFunctor D C} (A : DGAdjunction L R)

namespace CounitConeData

variable [IsPretriangulated D] (K : A.CounitConeData)

/-- **The twist triangle of a dg adjunction, as a functor on `H⁰`.**

`X ↦ (L R X ⟶ X ⟶ T X ⟶ (L R X)⟦1⟧)`, with `T` the twist candidate. -/
noncomputable def twistTriangleFunctor : H0 D ⥤ Triangle (H0 D) :=
  K.triangleFunctor A.counit_isClosed

/-- Every value of the twist triangle functor is distinguished. -/
theorem twistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 D) :
    (twistTriangleFunctor A K).obj X ∈ H0.distinguishedTriangles D :=
  K.triangleFunctor_obj_mem_distinguishedTriangles A.counit_isClosed X

@[simp]
theorem twistTriangleFunctor_obj_obj₁ (X : H0 D) :
    ((twistTriangleFunctor A K).obj X).obj₁ = (R.comp L).h0.obj X :=
  rfl

@[simp]
theorem twistTriangleFunctor_obj_obj₂ (X : H0 D) :
    ((twistTriangleFunctor A K).obj X).obj₂ = X :=
  rfl

@[simp]
theorem twistTriangleFunctor_obj_obj₃ (X : H0 D) :
    ((twistTriangleFunctor A K).obj X).obj₃ = K.twist.h0.obj X :=
  rfl

/-- **The first map is the counit, read on `H⁰`.** -/
theorem twistTriangleFunctor_obj_mor₁ (X : H0 D) :
    ((twistTriangleFunctor A K).obj X).mor₁ = A.h0Counit.app X :=
  (A.h0Counit_app X).symm

/-- **The second map is the canonical inclusion `id_D ⟶ T`.** -/
theorem twistTriangleFunctor_obj_mor₂ (X : H0 D) :
    ((twistTriangleFunctor A K).obj X).mor₂ =
      (DGFunctor.HomogeneousNatTrans.h0 K.inclusion K.inclusion_isClosed).app X :=
  rfl

@[simp]
theorem twistTriangleFunctor_map_hom₁ {X Y : H0 D} (f : X ⟶ Y) :
    ((twistTriangleFunctor A K).map f).hom₁ = (R.comp L).h0.map f :=
  rfl

@[simp]
theorem twistTriangleFunctor_map_hom₃ {X Y : H0 D} (f : X ⟶ Y) :
    ((twistTriangleFunctor A K).map f).hom₃ = K.twist.h0.map f :=
  rfl

/-- **The twist triangle does not depend on the chosen cones.** -/
noncomputable def twistTriangleIso (K K' : A.CounitConeData) :
    twistTriangleFunctor A K ≅ twistTriangleFunctor A K' :=
  DGFunctor.HomogeneousNatTrans.ConeData.compareIso A.counit_isClosed K K'

end CounitConeData

namespace UnitConeData

variable [IsPretriangulated C] (K : A.UnitConeData)

/-- **The unit triangle of a dg adjunction, as a functor on `H⁰`.**

`X ↦ (X ⟶ R L X ⟶ C X ⟶ X⟦1⟧)`, with `C` the *unshifted* cone of the unit.
The conventional cotwist is a shift of `C`, which this file does not take. -/
noncomputable def unitTriangleFunctor : H0 C ⥤ Triangle (H0 C) :=
  K.triangleFunctor A.unit_isClosed

/-- Every value of the unit triangle functor is distinguished. -/
theorem unitTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 C) :
    (unitTriangleFunctor A K).obj X ∈ H0.distinguishedTriangles C :=
  K.triangleFunctor_obj_mem_distinguishedTriangles A.unit_isClosed X

@[simp]
theorem unitTriangleFunctor_obj_obj₁ (X : H0 C) :
    ((unitTriangleFunctor A K).obj X).obj₁ = X :=
  rfl

@[simp]
theorem unitTriangleFunctor_obj_obj₂ (X : H0 C) :
    ((unitTriangleFunctor A K).obj X).obj₂ = (L.comp R).h0.obj X :=
  rfl

@[simp]
theorem unitTriangleFunctor_obj_obj₃ (X : H0 C) :
    ((unitTriangleFunctor A K).obj X).obj₃ = K.unitCone.h0.obj X :=
  rfl

/-- **The first map is the unit, read on `H⁰`.** -/
theorem unitTriangleFunctor_obj_mor₁ (X : H0 C) :
    ((unitTriangleFunctor A K).obj X).mor₁ = A.h0Unit.app X :=
  (A.h0Unit_app X).symm

/-- **The unit triangle does not depend on the chosen cones.** -/
noncomputable def unitTriangleIso (K K' : A.UnitConeData) :
    unitTriangleFunctor A K ≅ unitTriangleFunctor A K' :=
  DGFunctor.HomogeneousNatTrans.ConeData.compareIso A.unit_isClosed K K'

end UnitConeData

end DGAdjunction

end CategoryTheory
