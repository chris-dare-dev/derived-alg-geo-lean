/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationCone

/-!
# The twist triangle of an object

The evaluation map of an `EvaluationData E` is a closed degree-zero dg natural
transformation `RHom(E,-) ⊗ E ⟶ id`, and a choice of objectwise cones for it is
`TwistConeData`, whose cone functor is the twist `T_E`.  Feeding that choice to
`ConeData.triangleFunctor` gives

`H⁰ C ⥤ Triangle (H⁰ C)`,   `X ↦ (RHom(E,X) ⊗ E ⟶ X ⟶ T_E X ⟶ (RHom(E,X) ⊗ E)⟦1⟧)`,

every value distinguished.  This is the Seidel--Thomas twist triangle of an
object, read as a triangle of functors on `H⁰` rather than object by object.

## How this differs from the adjunction twist triangle

`DGAdjunction.CounitConeData.twistTriangleFunctor` is the same construction for
the counit of a dg adjunction.  Anno--Logvinenko's twist is that one; the
Seidel--Thomas twist of an object is this one.  They agree when `RHom(E,-)` and
`- ⊗ E` are the adjoint pair of a spherical functor out of `Perf(k)`, which the
repository cannot state: it has no `Perf(k)` as a dg category.  So the two twist
triangles coexist and neither is derived from the other.

## What is claimed, and what is not

That the triangle is functorial, that every value is distinguished, and that it
does not depend on the chosen cones (`twistTriangleIso`).  All three come from
the generic cone-triangle layer; the only input beyond it is that evaluation is
closed.

`twistH0IsTriangulated` adds that `H⁰(T_E)` is a triangulated functor, on the
one hypothesis that `RHom(E,-) ⊗ E` preserves chosen cones.  The shift half is
free: `DGFunctor.preservesShifts` holds for every dg functor, because a shift
element is a two-sided invertible element.  The cone half is not, and stays
open: `PreservesChosenCones` asks that maps *into* the cone split, while
`IsCopowerOf` only controls maps out.  See the discussion in
`DGCategory/Pretriangulated/ObjectTwist.lean`.

Nothing here says `T_E` is an autoequivalence, calls `E` spherical, or connects
it to `SerreFunctor.IsSphericalObject`.  Nothing here even produces an
`EvaluationData`: a dg category with enough copowers has to supply one.  Being
exact is not being invertible, and the object twist has no invertibility
statement at all -- the adjunction twist gets one from
`TwistCotwistEquivalenceConditions`, which has no object-level counterpart.

## Where the first two maps come from

`twistTriangleFunctor_obj_mor₁` identifies the first map with evaluation read on
`H⁰`, and `..._mor₂` identifies the second with the canonical inclusion
`id ⟶ T_E`.  As with the adjunction twist, the triangle's maps are the data
already present, not new choices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace EvaluationData

variable {C : Type u} [DGCategory.{v} C] {E : C} {V : EvaluationData E}

namespace TwistConeData

variable [IsPretriangulated C] (K : V.TwistConeData)

/-- **The twist triangle of an object, as a functor on `H⁰`.**

`X ↦ (RHom(E,X) ⊗ E ⟶ X ⟶ T_E X ⟶ (RHom(E,X) ⊗ E)⟦1⟧)`. -/
noncomputable def twistTriangleFunctor : H0 C ⥤ Triangle (H0 C) :=
  K.triangleFunctor V.evaluation_isClosed

/-- Every value of the object twist triangle functor is distinguished. -/
theorem twistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 C) :
    (twistTriangleFunctor K).obj X ∈ H0.distinguishedTriangles C :=
  K.triangleFunctor_obj_mem_distinguishedTriangles V.evaluation_isClosed X

@[simp]
theorem twistTriangleFunctor_obj_obj₁ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).obj₁ = V.functor.h0.obj X :=
  rfl

@[simp]
theorem twistTriangleFunctor_obj_obj₂ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).obj₂ = X :=
  rfl

@[simp]
theorem twistTriangleFunctor_obj_obj₃ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).obj₃ = K.twist.h0.obj X :=
  rfl

/-- **The first map is evaluation, read on `H⁰`.** -/
theorem twistTriangleFunctor_obj_mor₁ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).mor₁ =
      (DGFunctor.HomogeneousNatTrans.h0 V.evaluation V.evaluation_isClosed).app X :=
  rfl

/-- **The second map is the canonical inclusion `id ⟶ T_E`.** -/
theorem twistTriangleFunctor_obj_mor₂ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).mor₂ =
      (DGFunctor.HomogeneousNatTrans.h0 K.inclusion K.inclusion_isClosed).app X :=
  rfl

@[simp]
theorem twistTriangleFunctor_map_hom₁ {X Y : H0 C} (f : X ⟶ Y) :
    ((twistTriangleFunctor K).map f).hom₁ = V.functor.h0.map f :=
  rfl

@[simp]
theorem twistTriangleFunctor_map_hom₃ {X Y : H0 C} (f : X ⟶ Y) :
    ((twistTriangleFunctor K).map f).hom₃ = K.twist.h0.map f :=
  rfl

/-- **`H⁰(T_E)` commutes with the shift.**

`DGFunctor.commShift` spends the dg-level shift preservation on the ordinary
functor; `twistH0IsTriangulated` adds the cone half. -/
@[reducible]
noncomputable def twistH0CommShift : K.twist.h0.CommShift ℤ :=
  DGFunctor.commShift _ K.preservesShifts

/-- **The object twist is exact on `H⁰`.**

Both dg-level capabilities are available for the twist as soon as they are
available for `RHom(E,-) ⊗ E`, so `H⁰` of the twist commutes with the shift and
carries distinguished triangles to distinguished triangles.

This is exactness, not invertibility: nothing here says `T_E` is an
equivalence. -/
theorem twistH0IsTriangulated
    (hVc : DGFunctor.PreservesChosenCones V.functor) :
    letI : K.twist.h0.CommShift ℤ := DGFunctor.commShift _ K.preservesShifts
    K.twist.h0.IsTriangulated :=
  DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
    K.preservesShifts (K.preservesChosenCones hVc)

/-- **The object twist triangle does not depend on the chosen cones.** -/
noncomputable def twistTriangleIso (K K' : V.TwistConeData) :
    twistTriangleFunctor K ≅ twistTriangleFunctor K' :=
  DGFunctor.HomogeneousNatTrans.ConeData.compareIso V.evaluation_isClosed K K'

end TwistConeData

end EvaluationData

end CategoryTheory
