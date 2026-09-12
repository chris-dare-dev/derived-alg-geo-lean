/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup

/-!
# Numerical Grothendieck-group action of an object twist

The generic functorial-cone `K₀` interface computes the class of an object
twist as

`[T_E X] = [X] - [RHom(E,X) ⊗ E]`.

To identify this categorical formula with the numerical endomorphism `twistK₀`,
one further input is genuinely needed: the chosen copower must have class
`χ(E,X) • [E]`.  `EvaluationData.IsEulerCopower` names exactly that
capability, using the fixed-source descended character `chiRight` so that the
generic statement retains Hom-finiteness and finite Ext-amplitude without
requiring every shift functor to be linear.  It is invariant under the
canonical comparison between evaluation-data choices.  The full
shift-linearity needed by the two-variable numerical endomorphism remains
local to this spherical-twist consumer.

The capability and the categorical subtraction formula live in the generic
DG-enhancement layer.  This spherical-twist consumer contains only their two
comparisons with the pre-existing numerical formula.  It does not manufacture
the capability from additive `IsCopowerOf`; constructing the scalar-linear
realization layer remains a separate seam.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace EvaluationData

variable {C : Type u} [DGCategory.{v} C] [IsPretriangulated C] {E : C}

variable (k : Type w) [DivisionRing k] [Linear k (H0 C)]
  [HomFiniteBounded k (H0 C)]
  [∀ n : ℤ, (shiftFunctor (H0 C) n).Linear k]

namespace TwistConeData

variable {V : EvaluationData E} (K : V.TwistConeData)

/-- Under the Euler copower formula, the class computed by the evaluation
triangle is the existing numerical `twistK₀` formula on object classes. -/
theorem twistK₀Of_eq_twistK₀ (hV : V.IsEulerCopower k) (X : H0 C) :
    K₀.of (H0 C) (K.twist.h0.obj X) =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E)
        (K₀.of (H0 C) X) := by
  rw [SphericalTwist.twistK₀_of,
    K.twistK₀Of, hV X, chiRight_of]

set_option backward.isDefEq.respectTransparency false in
/-- If the evaluation functor is exact and realizes the Euler copower formula,
the induced map of the object twist is exactly the existing numerical
endomorphism `twistK₀`. -/
theorem twistK₀Map_eq_twistK₀
    (hVc : DGFunctor.PreservesChosenCones V.functor)
    (hV : V.IsEulerCopower k) :
    letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
    letI : K.twist.h0.IsTriangulated := K.twistH0IsTriangulated hVc
    K₀.map K.twist.h0 =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E) := by
  letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
  letI : K.twist.h0.IsTriangulated := K.twistH0IsTriangulated hVc
  apply K₀.hom_ext
  intro X
  rw [K₀.map_of]
  exact K.twistK₀Of_eq_twistK₀ k hV X

end TwistConeData

end EvaluationData

end CategoryTheory
