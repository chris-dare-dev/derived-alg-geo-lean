/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeKFlatSLinearity
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FlatPullback

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

/-- The missing geometric flat-base-change theorem, stated once with the two
flatness alternatives used in Proposition 3.15.

This is deliberately stronger than accepting an unrelated isomorphism at
each call site: an implementation must produce faithful base change uniformly
from flatness of either the source morphism `X → S` or the base-change
morphism `T → S`. -/
structure DqcFlatBaseChangeTheorem
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T)) where
  /-- Flatness of `X → S` gives derived base change. -/
  of_source_flat [Flat X.hom] :
    D.DqcFaithfulBaseChange pullBase pushBase pushFst
  /-- Flatness of `T → S` gives derived base change. -/
  of_base_flat [Flat T.hom] :
    D.DqcFaithfulBaseChange pullBase pushBase pushFst

/-- The two projections from `X ×_S T` form the defining pullback square
over the identity object of `Over S`. -/
theorem baseChangeProjections_isPullback :
    IsPullback (baseChangeSnd X T) (baseChangeFst X T)
      (toIdentityBaseChange T) (toIdentityBaseChange X) := by
  apply IsPullback.mk'
  · apply Over.OverMorphism.ext
    exact (Over.w (baseChangeSnd X T)).trans
      (Over.w (baseChangeFst X T)).symm
  · intro Z f g hSnd hFst
    apply Limits.prod.hom_ext
    · exact hFst
    · exact hSnd
  · intro Z f g h
    exact ⟨Limits.prod.lift g f, Limits.prod.lift_snd _ _,
      Limits.prod.lift_fst _ _⟩

namespace DqcFlatBaseChangeTheorem

/-- Under flatness of `X → S`, its pullback projection
`X_T → T` is flat. -/
theorem baseChangeSnd_flat
    [Flat X.hom] : Flat (baseChangeSnd X T).left := by
  exact MorphismProperty.of_isPullback (P := @Flat)
    ((Over.forget S).map_isPullback
      (baseChangeProjections_isPullback (X := X) (T := T)).flip)
    (by change Flat X.hom; infer_instance)

/-- Under flatness of `T → S`, its pullback projection
`X_T → X` is flat. -/
theorem baseChangeFst_flat
    [Flat T.hom] : Flat (baseChangeFst X T).left := by
  exact MorphismProperty.of_isPullback (P := @Flat)
    ((Over.forget S).map_isPullback
      (baseChangeProjections_isPullback (X := X) (T := T)))
    (by change Flat T.hom; infer_instance)

/-- Specialize the flat-base-change theorem using flatness of `X → S`. -/
def faithfulOfSourceFlat
    {pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X)}
    {pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T)}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (H : D.DqcFlatBaseChangeTheorem pullBase pushBase pushFst)
    [Flat X.hom] :
    D.DqcFaithfulBaseChange pullBase pushBase pushFst :=
  H.of_source_flat

/-- Specialize the flat-base-change theorem using flatness of `T → S`. -/
def faithfulOfBaseFlat
    {pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X)}
    {pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T)}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (H : D.DqcFlatBaseChangeTheorem pullBase pushBase pushFst)
    [Flat T.hom] :
    D.DqcFaithfulBaseChange pullBase pushBase pushFst :=
  H.of_base_flat

end DqcFlatBaseChangeTheorem

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

/-- The K-flat coefficient route under the paper's first flatness
alternative, flatness of `X → S`. -/
theorem perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_sourceFlat
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
    [Flat X.hom]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (flatBaseChange : D.DqcFlatBaseChangeTheorem
      B.pullback pushBase pushFst)
    (C : CompactFiberProjectionFormula.FiberCoefficientData
      (D := D) P)
    (hS : SourceTensorData.KFlatDqcSLinearComponents
      (D := D) Q B A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_faithfulBaseChange
    A hA hIso H Q B pushBase pushFst adj P
      flatBaseChange.faithfulOfSourceFlat C hS

/-- The K-flat coefficient route under the paper's second flatness
alternative, flatness of `T → S`. -/
theorem perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_baseFlat
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
    [Flat T.hom]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (flatBaseChange : D.DqcFlatBaseChangeTheorem
      B.pullback pushBase pushFst)
    (C : CompactFiberProjectionFormula.FiberCoefficientData
      (D := D) P)
    (hS : SourceTensorData.KFlatDqcSLinearComponents
      (D := D) Q B A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_faithfulBaseChange
    A hA hIso H Q B pushBase pushFst adj P
      flatBaseChange.faithfulOfBaseFlat C hS

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
