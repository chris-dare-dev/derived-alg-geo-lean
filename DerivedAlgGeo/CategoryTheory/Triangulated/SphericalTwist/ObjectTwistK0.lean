/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.ObjectTwistData

/-!
# Numerical Grothendieck-group action of an object twist

The generic functorial-cone `K₀` interface computes the class of an object
twist as

`[T_E X] = [X] - [RHom(E,X) ⊗ E]`.

To identify this categorical formula with the numerical endomorphism `twistK₀`,
one further input is genuinely needed: the chosen copower must have class
`χ(E,X) • [E]`.  `EvaluationData.IsEulerCopower` specializes the shared
objectwise rank-one `K₀` capability, using the fixed-source descended character
`chiRight` so that the generic statement retains Hom-finiteness and finite
Ext-amplitude without requiring every shift functor to be linear.  It is
invariant under the canonical comparison between evaluation-data choices.  The full
shift-linearity needed by the two-variable numerical endomorphism remains
local to this spherical-twist consumer.

The capability and the categorical subtraction formula live in the generic
DG-enhancement layer.  This spherical-twist consumer contains only their two
comparisons with the pre-existing numerical formula.  It does not manufacture
the capability from additive `IsCopowerOf`.  The scalar-linear realization now
proves the parallel predicate from explicitly supplied finite cohomology
presentations, but no adapter identifies its evaluation data with this additive
package; any such passage remains explicit.
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
  rw [SphericalTwist.twistK₀_apply, chiK₀_of]
  exact (K.toSphericalTwistData k hV).class_T_eq_sub_chiRight_smul X

/-- If evaluation realizes the Euler copower formula, the induced object-twist
map is the existing numerical endomorphism `twistK₀`. It is the induced-map theorem of the twist
data built by `CategoryTheory.EvaluationData.TwistConeData.toSphericalTwistData`. -/
theorem twistK₀Map_eq_twistK₀
    (hV : V.IsEulerCopower k) :
    letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
    letI : K.twist.h0.IsTriangulated := K.twistH0IsTriangulated
    K₀.map K.twist.h0 =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E) :=
  (K.toSphericalTwistData k hV).map_eq_twistK₀

end TwistConeData

end EvaluationData

end CategoryTheory
