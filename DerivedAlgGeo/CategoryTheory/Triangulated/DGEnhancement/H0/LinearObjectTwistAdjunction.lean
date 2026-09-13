/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearObjectTwistAdjunction
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearObjectTwist

/-!
# Scalar-linear object-twist triangles as adjunction twist triangles

The scalar-linear object-twist triangle for the selected copowers is
definitionally the counit-twist triangle of the copower--Hom dg adjunction.
For arbitrary scalar-linear evaluation data, the strict dg comparison descends
to a natural isomorphism of the full triangle functors on `H⁰`.

The first component is the canonical comparison to the selected evaluation
functor, the second is the identity, and the third is the `H⁰` image of the
dg twist comparison.  This identifies two presentations of the same twist
candidate; it supplies neither an autoequivalence nor sphericality.
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
  [DGLinear k C] [HasLinearCopowers k C]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- For the selected scalar-linear evaluation, the object-twist triangle and
the copower--Hom adjunction's counit-twist triangle are definitionally the
same functor. -/
theorem twistTriangleFunctor_eq_adjunctionTwistTriangleFunctor
    (K : (LinearEvaluationData.ofHasLinearCopowers k E).TwistConeData k) :
    twistTriangleFunctor K =
      DGAdjunction.CounitConeData.twistTriangleFunctor
        (linearCopowerAdjunction k E) K :=
  rfl

/-- The canonical identification of an arbitrary scalar-linear object-twist
triangle with the counit-twist triangle of the selected copower--Hom dg
adjunction. -/
noncomputable def adjunctionTwistTriangleIso
    (L : (linearCopowerAdjunction k E).CounitConeData) :
    twistTriangleFunctor K ≅
      DGAdjunction.CounitConeData.twistTriangleFunctor
        (linearCopowerAdjunction k E) L :=
  K.twistTriangleIsoOfEvaluation L

/-- On first vertices, the adjunction-triangle identification is the `H⁰`
image of the canonical comparison to the selected evaluation functor. -/
theorem adjunctionTwistTriangleIso_hom_app_hom₁
    (L : (linearCopowerAdjunction k E).CounitConeData) (X : H0 C) :
    ((K.adjunctionTwistTriangleIso L).hom.app X).hom₁ =
      (DGFunctor.h0Iso (LinearEvaluationData.compareIso V
        (LinearEvaluationData.ofHasLinearCopowers k E))).hom.app X :=
  rfl

/-- On middle vertices, the adjunction-triangle identification is the
identity. -/
theorem adjunctionTwistTriangleIso_hom_app_hom₂
    (L : (linearCopowerAdjunction k E).CounitConeData) (X : H0 C) :
    ((K.adjunctionTwistTriangleIso L).hom.app X).hom₂ = 𝟙 X :=
  K.twistTriangleIsoOfEvaluation_hom_app_hom₂ L X

/-- On third vertices, the comparison is the `H⁰` image of the dg
object-twist/adjunction-twist identification. -/
theorem adjunctionTwistTriangleIso_hom_app_hom₃
    (L : (linearCopowerAdjunction k E).CounitConeData) (X : H0 C) :
    ((K.adjunctionTwistTriangleIso L).hom.app X).hom₃ =
      (DGFunctor.h0Iso (K.adjunctionTwistIso L)).hom.app X :=
  K.twistTriangleIsoOfEvaluation_hom_app_hom₃ L X

/-- For a selected cone compared with itself, the identification of the two
triangle presentations is the identity. -/
theorem adjunctionTwistTriangleIso_self
    (K : (LinearEvaluationData.ofHasLinearCopowers k E).TwistConeData k) :
    K.adjunctionTwistTriangleIso K = Iso.refl _ :=
  K.twistTriangleIsoOfEvaluation_self

/-- Changing scalar-linear evaluation data first and then identifying the
adjunction presentation gives the direct triangle identification. -/
theorem twistTriangleIsoOfEvaluation_trans_adjunctionTwistTriangleIso
    {W : LinearEvaluationData k E} (L : W.TwistConeData k)
    (M : (linearCopowerAdjunction k E).CounitConeData) :
    (K.twistTriangleIsoOfEvaluation L).trans
        (L.adjunctionTwistTriangleIso M) =
      K.adjunctionTwistTriangleIso M :=
  K.twistTriangleIsoOfEvaluation_trans L M

end LinearEvaluationData.TwistConeData

end CategoryTheory
