/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup

/-!
# Grothendieck-group action of an object twist

The distinguished evaluation triangle always computes the class of an object
twist as

`[T_E X] = [X] - [RHom(E,X) ⊗ E]`.

To identify this categorical formula with the numerical reflection `twistK₀`,
one further input is genuinely needed: the chosen copower must have class
`χ(E,X) • [E]`.  `EvaluationData.IsEulerCopower` names exactly that
capability, using the already descended Euler form `chiK₀` so that the
statement cannot be instantiated without Hom-finiteness and finite
Ext-amplitude.  It is invariant under the canonical comparison between
evaluation-data choices.

This file proves every downstream `K₀` consequence of that capability.  It
does not manufacture the capability from `IsCopowerOf`: that existing
universal property represents additive cochains over `ℤ`, whereas the Euler
coefficient measures dimensions over `k`.  Even after a scalar-linear copower
interface is supplied, an Euler-class computation needs homotopy invariance and
a finite decomposition of the Hom-complex copower into shifted finite sums of
`E`.  Constructing that linear realization layer is the remaining seam.
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
  have h := K₀.of_triangle (H0 C) ((K.twistTriangleFunctor).obj X)
    (K.twistTriangleFunctor_obj_mem_distinguishedTriangles X)
  change K₀.of (H0 C) X =
    K₀.of (H0 C) (V.functor.h0.obj X) +
      K₀.of (H0 C) (K.twist.h0.obj X) at h
  rw [h]
  abel

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

section Euler

variable (k : Type w) [DivisionRing k] [Linear k (H0 C)]
  [HomFiniteBounded k (H0 C)]
  [∀ n : ℤ, (shiftFunctor (H0 C) n).Linear k]

/-- An evaluation choice realizes the Euler copower formula when
`[RHom(E,X) ⊗ E] = χ(E,X) • [E]` for every `X`.

The coefficient is stated with `chiK₀`, rather than junk-total `chiHom`, so
Hom-finiteness and finite Ext-amplitude are part of the contract. -/
def IsEulerCopower (V : EvaluationData E) : Prop :=
  ∀ X : H0 C,
    K₀.of (H0 C) (V.functor.h0.obj X) =
      chiK₀ k (H0 C) (K₀.of (H0 C) (show H0 C from E))
          (K₀.of (H0 C) X) •
        K₀.of (H0 C) (show H0 C from E)

/-- The Euler copower formula is independent of the chosen evaluation data. -/
theorem IsEulerCopower.ofCompare {V W : EvaluationData E}
    (hV : V.IsEulerCopower k) : W.IsEulerCopower k := by
  intro X
  rw [← hV X]
  exact (K₀.of_iso (H0 C) ((DGFunctor.h0Iso (V.compareIso W)).app X)).symm

namespace TwistConeData

variable {V : EvaluationData E} (K : V.TwistConeData)

/-- Under the Euler copower formula, the class computed by the evaluation
triangle is the existing numerical `twistK₀` formula on object classes. -/
theorem twistK₀Of_eq_twistK₀ (hV : V.IsEulerCopower k) (X : H0 C) :
    K₀.of (H0 C) (K.twist.h0.obj X) =
      SphericalTwist.twistK₀ k (H0 C) (show H0 C from E)
        (K₀.of (H0 C) X) := by
  rw [SphericalTwist.twistK₀_of, K.twistK₀Of, hV X,
    chiK₀_of_of]

set_option backward.isDefEq.respectTransparency false in
/-- If the evaluation functor is exact and realizes the Euler copower formula,
the induced map of the object twist is exactly the existing numerical
reflection `twistK₀`. -/
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

end Euler

end EvaluationData

end CategoryTheory
