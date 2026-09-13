/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationCone

/-!
# The scalar-linear object-twist triangle

For scalar-linear evaluation data, a choice of objectwise cones gives the
functorial triangle

`Hom(E,X) ⊗ E ⟶ X ⟶ T_E X ⟶ (Hom(E,X) ⊗ E)⟦1⟧`

on `H⁰`.  Every value is distinguished.  The construction is the existing
generic cone-triangle functor, and the comparison across evaluation and cone
choices is the existing strict-square comparison.

This file is the scalar-linear analogue of the additive object-twist triangle;
it does not assert that the two evaluation packages agree.  Nor does it claim
that the twist is invertible or that the object is spherical.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace LinearEvaluationData.TwistConeData

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- The scalar-linear object-twist triangle as a functor on `H⁰`. -/
noncomputable def twistTriangleFunctor : H0 C ⥤ Triangle (H0 C) :=
  K.triangleFunctor V.evaluation_isClosed

/-- The generic cone construction makes the displayed family pointwise
distinguished; this is the bridge used by triangle and `K₀` consumers. -/
theorem twistTriangleFunctor_obj_mem_distinguishedTriangles (X : H0 C) :
    (twistTriangleFunctor K).obj X ∈ H0.distinguishedTriangles C :=
  K.triangleFunctor_obj_mem_distinguishedTriangles V.evaluation_isClosed X

/-- The first vertex retains the chosen scalar-linear evaluation functor, so
downstream formulas can rewrite it without unfolding the cone construction. -/
@[simp]
theorem twistTriangleFunctor_obj_obj₁ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).obj₁ = V.functor.h0.obj X :=
  rfl

/-- The middle vertex is the original object, definitionally. -/
@[simp]
theorem twistTriangleFunctor_obj_obj₂ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).obj₂ = X :=
  rfl

/-- This projection keeps exactness and `K₀` consumers in the normal form
`K.twist.h0` without unfolding the generic cone triangle. -/
@[simp]
theorem twistTriangleFunctor_obj_obj₃ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).obj₃ = K.twist.h0.obj X :=
  rfl

/-- The cone triangle reuses the existing evaluation transformation on `H⁰`;
it does not introduce a second object-twist arrow. -/
theorem twistTriangleFunctor_obj_mor₁ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).mor₁ =
      (DGFunctor.HomogeneousNatTrans.h0 V.evaluation
        V.evaluation_isClosed).app X :=
  rfl

/-- The second map is definitionally the generic cone inclusion, so the
dg-level strict inclusion comparisons descend without another compatibility
proof. -/
theorem twistTriangleFunctor_obj_mor₂ (X : H0 C) :
    ((twistTriangleFunctor K).obj X).mor₂ =
      (DGFunctor.HomogeneousNatTrans.h0 K.inr K.inr_isClosed).app X :=
  rfl

/-- Naturality on the first vertices is inherited from scalar-linear
evaluation. -/
@[simp]
theorem twistTriangleFunctor_map_hom₁ {X Y : H0 C} (f : X ⟶ Y) :
    ((twistTriangleFunctor K).map f).hom₁ = V.functor.h0.map f :=
  rfl

/-- Naturality on the third vertices is the `H⁰` action of the twist dg
functor. -/
@[simp]
theorem twistTriangleFunctor_map_hom₃ {X Y : H0 C} (f : X ⟶ Y) :
    ((twistTriangleFunctor K).map f).hom₃ = K.twist.h0.map f :=
  rfl

/-- The canonical shift comparison for `H⁰` of the scalar-linear object
twist. -/
@[reducible]
noncomputable def twistH0CommShift : K.twist.h0.CommShift ℤ :=
  DGFunctor.h0CommShift K.twist

/-- The scalar-linear object twist is exact on `H⁰`.  This is independent
of, and weaker than, invertibility. -/
theorem twistH0IsTriangulated :
    letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
    K.twist.h0.IsTriangulated :=
  DGFunctor.h0IsTriangulated K.twist

/-- The scalar-linear object-twist triangle does not depend on its cone
choice. -/
noncomputable def twistTriangleIso (K K' : V.TwistConeData k) :
    twistTriangleFunctor K ≅ twistTriangleFunctor K' :=
  DGFunctor.HomogeneousNatTrans.ConeData.compareIso
    V.evaluation_isClosed K K'

/-- The scalar-linear object-twist triangle does not depend on either the
evaluation data or the cone choices. -/
noncomputable def twistTriangleIsoOfEvaluation
    {W : LinearEvaluationData k E} (L : W.TwistConeData k) :
    twistTriangleFunctor K ≅ twistTriangleFunctor L :=
  DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare
    K V.evaluation_isClosed L W.evaluation_isClosed
    (LinearEvaluationData.compareIso V W)
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))
    (V.compare_evaluation_square k W)

/-- The first component of the triangle comparison is the `H⁰` image of the
canonical scalar-linear evaluation comparison. -/
@[simp]
theorem twistTriangleIsoOfEvaluation_hom_app_hom₁
    {W : LinearEvaluationData k E} (L : W.TwistConeData k) (X : H0 C) :
    ((K.twistTriangleIsoOfEvaluation L).hom.app X).hom₁ =
      (DGFunctor.h0Iso (LinearEvaluationData.compareIso V W)).hom.app X :=
  rfl

/-- The middle component of the triangle comparison is the identity. -/
@[simp]
theorem twistTriangleIsoOfEvaluation_hom_app_hom₂
    {W : LinearEvaluationData k E} (L : W.TwistConeData k) (X : H0 C) :
    ((K.twistTriangleIsoOfEvaluation L).hom.app X).hom₂ = 𝟙 X := by
  change (DGFunctor.h0Iso
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))).hom.app X = 𝟙 X
  rw [DGFunctor.h0Iso_refl]
  rfl

/-- The third component is the `H⁰` image of the strict cone-functor
comparison. -/
@[simp]
theorem twistTriangleIsoOfEvaluation_hom_app_hom₃
    {W : LinearEvaluationData k E} (L : W.TwistConeData k) (X : H0 C) :
    ((K.twistTriangleIsoOfEvaluation L).hom.app X).hom₃ =
      (DGFunctor.h0Iso (K.compareIso L)).hom.app X :=
  DGFunctor.HomogeneousNatTrans.ConeData.triangleIsoOfStrictSquare_hom_app_hom₃
    K V.evaluation_isClosed L W.evaluation_isClosed
    (LinearEvaluationData.compareIso V W)
    (Iso.refl (show Z0 (DGFunctor C C) from DGFunctor.id C))
    (V.compare_evaluation_square k W) X

/-- Comparing a scalar-linear evaluation and cone choice with itself gives
the identity natural isomorphism of triangle functors. -/
@[simp]
theorem twistTriangleIsoOfEvaluation_self :
    K.twistTriangleIsoOfEvaluation K = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  refine Triangle.hom_ext _ _ ?_ ?_ ?_
  · change (DGFunctor.h0Iso (LinearEvaluationData.compareIso V V)).hom.app X =
      𝟙 (V.functor.h0.obj X)
    rw [LinearEvaluationData.compareIso_self,
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

/-- Scalar-linear twist-triangle comparisons compose coherently across both
evaluation and cone choices. -/
theorem twistTriangleIsoOfEvaluation_trans
    {W X : LinearEvaluationData k E}
    (L : W.TwistConeData k) (M : X.TwistConeData k) :
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
      ← LinearEvaluationData.compareIso_trans V W X, DGFunctor.h0Iso_trans]
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

end LinearEvaluationData.TwistConeData

end CategoryTheory
