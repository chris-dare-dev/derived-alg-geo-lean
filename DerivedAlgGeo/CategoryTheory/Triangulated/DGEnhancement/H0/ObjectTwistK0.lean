/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationConeK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.RankOne

/-!
# Euler-class realization for object-twist evaluation data

The existing `EvaluationData` gives additive copowers and the functor
`RHom(E,-) ⊗ E`.  Relating its object classes to the `k`-linear Euler form is
extra realization content: the current `IsCopowerOf` represents additive
cochains over `ℤ`, not `k`-linear cochains.

`EvaluationData.IsEulerCopower` specializes the shared rank-one `K₀` formula,
using the fixed-source descended character `chiRight`; this retains
Hom-finiteness and finite Ext-amplitude without imposing the stronger
shift-linearity needed to descend in the first variable as well.  The property
is independent of the chosen additive evaluation data.  The parallel direct
linear evaluation consumer uses the same numerical interface, but that common
formula supplies no map between additive and scalar-linear evaluation data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe w v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated Triangulated

namespace EvaluationData

variable {C : Type u} [DGCategory.{v} C] [IsPretriangulated C] {E : C}

namespace TwistConeData

variable {V : EvaluationData E} (K : V.TwistConeData)

/-- The object-twist triangle gives
`[T_E X] = [X] - [RHom(E,X) ⊗ E]` in `K₀(H⁰ C)`. -/
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
/-- If the evaluation functor preserves chosen cones, the object twist acts on
`K₀` by the identity minus the evaluation functor. -/
theorem twistK₀Map (hVc : DGFunctor.PreservesChosenCones V.functor) :
    letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
    letI : K.twist.h0.IsTriangulated := K.twistH0IsTriangulated hVc
    letI : V.functor.h0.CommShift ℤ :=
      DGFunctor.commShift _ (DGFunctor.preservesShifts _)
    letI : V.functor.h0.IsTriangulated :=
      DGFunctor.isTriangulated_of_preservesShifts_and_chosenCones _
        (DGFunctor.preservesShifts _) hVc
    K₀.map K.twist.h0 =
      AddMonoidHom.id (K₀ (H0 C)) - K₀.map V.functor.h0 := by
  letI : K.twist.h0.CommShift ℤ := K.twistH0CommShift
  letI : K.twist.h0.IsTriangulated := K.twistH0IsTriangulated hVc
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

end TwistConeData

variable (k : Type w) [DivisionRing k] [Linear k (H0 C)]
  [HomFiniteBounded k (H0 C)]

/-- An evaluation choice realizes the Euler copower formula when
`[RHom(E,X) ⊗ E] = χ(E,X) • [E]` for every `X`.

This is explicit realization input, not a consequence of the present
additive `IsCopowerOf` universal property. -/
def IsEulerCopower (V : EvaluationData E) : Prop :=
  K₀.IsRankOne V.functor.h0
    (chiRight k (H0 C) (show H0 C from E))
    (K₀.of (H0 C) (show H0 C from E))

/-- The Euler copower formula is independent of the chosen evaluation data. -/
theorem IsEulerCopower.ofCompare {V W : EvaluationData E}
    (hV : V.IsEulerCopower k) : W.IsEulerCopower k := by
  exact K₀.IsRankOne.ofIso hV (DGFunctor.h0Iso (V.compareIso W))

end EvaluationData

end CategoryTheory
