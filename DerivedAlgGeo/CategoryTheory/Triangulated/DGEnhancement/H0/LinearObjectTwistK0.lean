/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationConeK0

/-!
# Grothendieck-group action of a scalar-linear object twist

The generic functorial-cone formula specializes to scalar-linear evaluation:

`[T_E X] = [X] - [DGLinear.homComplex k E X ⊗ₖ E]`.

If the evaluation functor preserves chosen cones, the same identity holds for
the induced endomorphisms of `K₀`.  No Euler-characteristic identification is
used here; that numerical specialization belongs to `SphericalTwist`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace LinearEvaluationData.TwistConeData

variable {k : Type w} [CommRing k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- The scalar-linear object-twist triangle gives the identity-minus-evaluation
formula on object classes. -/
theorem twistK₀Of (X : H0 C) :
    K₀.of (H0 C) (K.twist.h0.obj X) =
      K₀.of (H0 C) X - K₀.of (H0 C) (V.functor.h0.obj X) := by
  calc
    K₀.of (H0 C) (K.twist.h0.obj X) =
        K₀.of (H0 C) ((DGFunctor.id C).h0.obj X) -
          K₀.of (H0 C) (V.functor.h0.obj X) :=
      K.functorK₀Of V.evaluation_isClosed X
    _ = K₀.of (H0 C) X - K₀.of (H0 C) (V.functor.h0.obj X) := by
      rw [K₀.of_iso (H0 C) ((DGFunctor.h0IdIso).app X)]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- If scalar-linear evaluation preserves chosen cones, the object twist acts
on `K₀` by the identity minus evaluation. -/
theorem twistK₀Map (hVc : DGFunctor.PreservesChosenCones V.functor) :
    letI : K.twist.h0.CommShift ℤ :=
      DGFunctor.commShift _ K.preservesShifts
    letI : K.twist.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        K.preservesShifts (K.preservesChosenCones hVc)
    letI : V.functor.h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : V.functor.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _) hVc
    K₀.map K.twist.h0 =
      AddMonoidHom.id (K₀ (H0 C)) - K₀.map V.functor.h0 := by
  letI : K.twist.h0.CommShift ℤ :=
    DGFunctor.commShift _ K.preservesShifts
  letI : K.twist.h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      K.preservesShifts (K.preservesChosenCones hVc)
  letI : V.functor.h0.CommShift ℤ :=
    DGFunctor.commShift _ (DGFunctor.preservesShifts _)
  letI : V.functor.h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      (DGFunctor.preservesShifts _) hVc
  apply K₀.hom_ext
  intro X
  change K₀.of (H0 C) (K.twist.h0.obj X) =
    K₀.of (H0 C) X - K₀.of (H0 C) (V.functor.h0.obj X)
  exact K.twistK₀Of X

end LinearEvaluationData.TwistConeData

end CategoryTheory
