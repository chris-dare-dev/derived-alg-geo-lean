/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement.LinearEvaluationK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.LinearObjectTwistK0

/-!
# Automatic numerical action of the scalar-linear object twist

The generic scalar-linear twist formulas consume an explicit
`LinearEvaluationData.IsEulerCopower` witness.  Over a field, finite bounded
H⁰ Hom-spaces and the existence of scalar-linear copowers now construct that
witness automatically, so the numerical Seidel--Thomas formula needs no
additional presentation data.

The endomorphism-level result still assumes that scalar-linear evaluation
preserves the chosen cones.  No exactness, sphericality, or autoequivalence is
inferred from Hom-finiteness or formality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace LinearEvaluationData.TwistConeData

variable (k : Type v) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)]
  [∀ n : ℤ, (shiftFunctor (H0 C) n).Linear k]
  [HasLinearCopowers k C]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- When all scalar-linear copowers exist, field formality and
`HomFiniteBounded` automatically identify the evaluation-cone class with the
numerical twist class. -/
theorem twistK₀Of_eq_twistK₀_ofHomFiniteBounded (X : H0 C) :
    K₀.of (H0 C) (K.twist.h0.obj X) =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E)
        (K₀.of (H0 C) X) :=
  K.twistK₀Of_eq_twistK₀ k
    (LinearEvaluationData.IsEulerCopower.ofHomFiniteBounded k V) X

set_option backward.isDefEq.respectTransparency false in
/-- If scalar-linear evaluation also preserves chosen cones, the induced
endomorphism is the numerical twist without a separately supplied Euler
copower witness. -/
theorem twistK₀Map_eq_twistK₀_ofHomFiniteBounded
    (hVc : DGFunctor.PreservesChosenCones V.functor) :
    letI : K.twist.h0.CommShift ℤ :=
      DGFunctor.commShift _ K.preservesShifts
    letI : K.twist.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        K.preservesShifts (K.preservesChosenCones hVc)
    K₀.map K.twist.h0 =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E) :=
  K.twistK₀Map_eq_twistK₀ k hVc
    (LinearEvaluationData.IsEulerCopower.ofHomFiniteBounded k V)

end LinearEvaluationData.TwistConeData

end CategoryTheory
