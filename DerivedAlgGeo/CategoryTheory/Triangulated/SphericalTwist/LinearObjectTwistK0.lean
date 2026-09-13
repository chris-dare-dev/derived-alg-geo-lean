/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearEvaluationK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup

/-!
# Numerical action of the scalar-linear object twist

The direct scalar-linear evaluation package now reaches the existing numerical
Seidel--Thomas formula without passing through additive `EvaluationData`.
`LinearEvaluationData.IsEulerCopower` identifies the evaluation term in the
generic cone subtraction formula with `χ(E,X) • [E]`.

Exactness is automatic for every dg functor.  The endomorphism-level theorem
still accepts a redundant cone-preservation argument for compatibility.  Nothing here compares
the additive and scalar-linear universal properties or asserts that the twist
is an autoequivalence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace LinearEvaluationData.TwistConeData

variable (k : Type w) [Field k]
  {C : Type u} [DGCategory.{v} C] [IsPretriangulated C]
  [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)]
  [DGLinear k C] [HomFiniteBounded k (H0 C)]
  [∀ n : ℤ, (shiftFunctor (H0 C) n).Linear k]
  {E : C} {V : LinearEvaluationData k E} (K : V.TwistConeData k)

/-- Under the scalar-linear Euler copower formula, the evaluation cone has the
existing numerical `twistK₀` class on every object. -/
theorem twistK₀Of_eq_twistK₀ (hV : V.IsEulerCopower k) (X : H0 C) :
    K₀.of (H0 C) (K.twist.h0.obj X) =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E)
        (K₀.of (H0 C) X) := by
  rw [SphericalTwist.twistK₀_of, K.twistK₀Of, hV X, chiRight_of]

set_option backward.isDefEq.respectTransparency false in
/-- If scalar-linear evaluation realizes the Euler copower formula, its cone
induces the numerical twist endomorphism on `K₀`.  The cone argument is
retained for compatibility and is redundant. -/
theorem twistK₀Map_eq_twistK₀
    (hVc : DGFunctor.PreservesChosenCones V.functor)
    (hV : V.IsEulerCopower k) :
    letI : K.twist.h0.CommShift ℤ :=
      DGFunctor.commShift _ K.preservesShifts
    letI : K.twist.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        K.preservesShifts (K.preservesChosenCones hVc)
    K₀.map K.twist.h0 =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E) := by
  letI : K.twist.h0.CommShift ℤ :=
    DGFunctor.commShift _ K.preservesShifts
  letI : K.twist.h0.IsTriangulated :=
    DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
      K.preservesShifts (K.preservesChosenCones hVc)
  apply K₀.hom_ext
  intro X
  rw [K₀.map_of]
  exact K.twistK₀Of_eq_twistK₀ k hV X

end LinearEvaluationData.TwistConeData

end CategoryTheory
