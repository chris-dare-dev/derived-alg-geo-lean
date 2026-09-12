/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeKFlatSLinearity

/-!
# Faithful base change for external-product coefficients

This file names the derived base-change isomorphism expressing that
`T → S` is faithful with respect to `X → S`:

`L(X → S)⁎ R(T → S)⁎ ≅ R(X_T → X)⁎ L(X_T → T)⁎`.

A coefficient object on `T` can therefore be pushed to `S` and pulled back
to `X`, where it agrees with the push-pull coefficient produced by the
first-projection formula. This constructs the quasicoherent base-coefficient
data used by `Dqc(S)`-linearity without imposing compactness on pushforward.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]

namespace KFlatBaseChangeData

/-- The derived base-change isomorphism saying that `T → S` is faithful
with respect to `X → S`.

Both pullbacks in the square are genuine derived pullbacks: the right-hand
one is the K-flat pullback bundled in `D`, while the left-hand one is supplied
explicitly (and can be constructed by `KFlatBasePullbackData`). -/
structure DqcFaithfulBaseChange
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T)) where
  /-- Pulling a fibre pushforward back to `X` agrees with pushing its pullback
  from `X_T` forward to `X`. -/
  iso : pushBase.functor ⋙ pullBase.functor ≅
    D.pullSnd.functor ⋙ pushFst.functor

namespace CompactFiberProjectionFormula

/-- A first-projection coefficient represented by a quasicoherent object on
`T`, before applying faithful base change.

In the geometric application this object is the tensor of the dual of the
earlier compact fibre factor with the later one, including the two shifts. -/
structure FiberCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst) where
  /-- The quasicoherent coefficient on `T`. -/
  fiberCoefficient :
    CompactDqcFiber T → CompactDqcFiber T → ℤ → ℤ → BaseDqc T.left
  /-- The coefficient on `X` is pushforward of the pullback of the fibre
  coefficient. -/
  coefficientIso (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    P.coefficient Gi Gj a b ≅
      pushFst.functor.obj
        (D.pullSnd.functor.obj (fiberCoefficient Gi Gj a b))

namespace FiberCoefficientData

/-- Faithful base change pushes a fibre coefficient to `S` and identifies
its pullback to `X` with the projection-formula coefficient. -/
def toDqcBaseCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    {P : D.CompactFiberProjectionFormula H Q pushFst}
    {pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X)}
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (faithful : D.DqcFaithfulBaseChange pullBase pushBase pushFst)
    (C : FiberCoefficientData (D := D) P) :
    DqcBaseCoefficientData (D := D) P pullBase where
  baseCoefficient Gi Gj a b :=
    pushBase.functor.obj (C.fiberCoefficient Gi Gj a b)
  coefficientIso Gi Gj a b :=
    C.coefficientIso Gi Gj a b ≪≫
      (faithful.iso.app (C.fiberCoefficient Gi Gj a b)).symm

end FiberCoefficientData

end CompactFiberProjectionFormula

/-- Faithful base change converts fibre coefficients into base coefficients;
`Dqc(S)`-linearity then proves perfect-component semiorthogonality. -/
theorem perfectComponentsSemiorthogonal_of_projectionFormula_of_faithfulBaseChange
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (faithful : D.DqcFaithfulBaseChange pullBase pushBase pushFst)
    (C : CompactFiberProjectionFormula.FiberCoefficientData
      (D := D) P)
    (hS : SourceTensorData.DqcSLinearComponents
      (D := D) Q pullBase A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_projectionFormula_of_dqcSLinear
    A hA hIso H Q pullBase pushFst adj P
      (CompactFiberProjectionFormula.FiberCoefficientData.toDqcBaseCoefficientData
        (D := D) pushBase faithful C) hS

/-- The faithful-base-change route with `L(X → S)⁎` constructed from a
K-flat resolution on the base. -/
theorem perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_faithfulBaseChange
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (faithful : D.DqcFaithfulBaseChange B.pullback pushBase pushFst)
    (C : CompactFiberProjectionFormula.FiberCoefficientData
      (D := D) P)
    (hS : SourceTensorData.KFlatDqcSLinearComponents
      (D := D) Q B A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_projectionFormula_of_faithfulBaseChange
    A hA hIso H Q B.pullback pushBase pushFst adj P faithful C hS

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
