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
does not depend on either the chosen evaluation data or the chosen cones
(`twistTriangleIsoOfEvaluation`).  The comparison is a natural isomorphism of
full triangle functors, with coherent identity and composition laws.  The
original `twistTriangleIso` remains the definitional wrapper for changing only
the cone choices.  All three facts come from the generic strict-square
cone-triangle layer; the only input beyond it is that evaluation is closed.

`H⁰(T_E)` is triangulated automatically: every dg functor preserves both
shift witnesses and the strong split cone witnesses.

Nothing here says `T_E` is an autoequivalence, calls `E` spherical, or connects
it to `SerreFunctor.IsSphericalObject`.  The generic `HasCopowers` capability
does produce `HasEvaluationData` and a noncomputably selected
`chosenEvaluationData`; what remains open is a concrete dg category carrying
that capability.  Being exact is not being an autoequivalence.  The comparison
maps between different choices are invertible, but the object twist functor
itself has no autoequivalence statement -- the adjunction twist gets one from
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

This is the object-twist name for the canonical dg-functor package. -/
@[reducible]
noncomputable def twistH0CommShift : K.twist.h0.CommShift ℤ :=
  DGFunctor.h0CommShift K.twist

/-- **The object twist is exact on `H⁰`.**

Both dg-level capabilities are available for every dg functor, so `H⁰` of the
twist commutes with the shift and carries distinguished triangles to
distinguished triangles.

This is exactness, not invertibility: nothing here says `T_E` is an
equivalence. -/
theorem twistH0IsTriangulated :
    letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
    K.twist.h0.IsTriangulated :=
  DGFunctor.h0IsTriangulated K.twist

/-- **The object twist triangle does not depend on the chosen cones.** -/
noncomputable def twistTriangleIso (K K' : V.TwistConeData) :
    twistTriangleFunctor K ≅ twistTriangleFunctor K' :=
  DGFunctor.HomogeneousNatTrans.ConeData.compareIso V.evaluation_isClosed K K'

/-- **The object twist triangle does not depend on the evaluation or cone
choices.**

The separately named definition preserves the original `twistTriangleIso`
contract, which remains the direct generic cone-choice comparison. -/
noncomputable def twistTriangleIsoOfEvaluation {W : EvaluationData E}
    (L : W.TwistConeData) :
    twistTriangleFunctor K ≅ twistTriangleFunctor L :=
  DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare
    K V.evaluation_isClosed L W.evaluation_isClosed
    (EvaluationData.compareIso V W)
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))
    (V.compare_evaluation_square W)

@[simp]
theorem twistTriangleIsoOfEvaluation_hom_app_hom₁ {W : EvaluationData E}
    (L : W.TwistConeData) (X : H0 C) :
    ((K.twistTriangleIsoOfEvaluation L).hom.app X).hom₁ =
      (DGFunctor.h0Iso (EvaluationData.compareIso V W)).hom.app X :=
  rfl

@[simp]
theorem twistTriangleIsoOfEvaluation_hom_app_hom₂ {W : EvaluationData E}
    (L : W.TwistConeData) (X : H0 C) :
    ((K.twistTriangleIsoOfEvaluation L).hom.app X).hom₂ = 𝟙 X := by
  change (DGFunctor.h0Iso
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))).hom.app X = 𝟙 X
  rw [DGFunctor.h0Iso_refl]
  rfl

@[simp]
theorem twistTriangleIsoOfEvaluation_hom_app_hom₃ {W : EvaluationData E}
    (L : W.TwistConeData) (X : H0 C) :
    ((K.twistTriangleIsoOfEvaluation L).hom.app X).hom₃ =
      (DGFunctor.h0Iso (K.compareIso L)).hom.app X :=
  DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare_hom_app_hom₃
    K V.evaluation_isClosed L W.evaluation_isClosed
    (EvaluationData.compareIso V W)
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))
    (V.compare_evaluation_square W) X

@[simp]
theorem twistTriangleIsoOfEvaluation_self :
    K.twistTriangleIsoOfEvaluation K = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  refine Triangle.hom_ext _ _ ?_ ?_ ?_
  · change (DGFunctor.h0Iso (V.compareIso V)).hom.app X =
      𝟙 (V.functor.h0.obj X)
    rw [EvaluationData.compareIso_self,
      DGFunctor.h0Iso_refl (C := C) (D := C)
        (show Z0 (DGFunctor C C) from V.functor)]
    rfl
  · change 𝟙 X = 𝟙 X
    rfl
  · rw [twistTriangleIsoOfEvaluation_hom_app_hom₃]
    change (DGFunctor.h0Iso (K.compareIso K)).hom.app X =
      𝟙 (K.twist.h0.obj X)
    rw [K.compareIso_self,
      DGFunctor.h0Iso_refl (C := C) (D := C)
        (show Z0 (DGFunctor C C) from K.twist)]
    rfl

theorem twistTriangleIsoOfEvaluation_trans {W X : EvaluationData E}
    (L : W.TwistConeData) (M : X.TwistConeData) :
    (K.twistTriangleIsoOfEvaluation L).trans
        (L.twistTriangleIsoOfEvaluation M) =
      K.twistTriangleIsoOfEvaluation M := by
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  refine Triangle.hom_ext _ _ ?_ ?_ ?_
  · change
      ((K.twistTriangleIsoOfEvaluation L).hom.app Y).hom₁ ≫
          ((L.twistTriangleIsoOfEvaluation M).hom.app Y).hom₁ =
        ((K.twistTriangleIsoOfEvaluation M).hom.app Y).hom₁
    rw [twistTriangleIsoOfEvaluation_hom_app_hom₁,
      twistTriangleIsoOfEvaluation_hom_app_hom₁,
      twistTriangleIsoOfEvaluation_hom_app_hom₁,
      ← EvaluationData.compareIso_trans V W X, DGFunctor.h0Iso_trans]
    rfl
  · change
      ((K.twistTriangleIsoOfEvaluation L).hom.app Y).hom₂ ≫
          ((L.twistTriangleIsoOfEvaluation M).hom.app Y).hom₂ =
        ((K.twistTriangleIsoOfEvaluation M).hom.app Y).hom₂
    rw [twistTriangleIsoOfEvaluation_hom_app_hom₂,
      twistTriangleIsoOfEvaluation_hom_app_hom₂,
      twistTriangleIsoOfEvaluation_hom_app_hom₂]
    exact Category.id_comp (X := Y) (Y := Y) (𝟙 Y)
  · change
      ((K.twistTriangleIsoOfEvaluation L).hom.app Y).hom₃ ≫
          ((L.twistTriangleIsoOfEvaluation M).hom.app Y).hom₃ =
        ((K.twistTriangleIsoOfEvaluation M).hom.app Y).hom₃
    rw [twistTriangleIsoOfEvaluation_hom_app_hom₃,
      twistTriangleIsoOfEvaluation_hom_app_hom₃,
      twistTriangleIsoOfEvaluation_hom_app_hom₃,
      ← K.compareIso_trans L M, DGFunctor.h0Iso_trans]
    rfl

end TwistConeData

end EvaluationData

end CategoryTheory
