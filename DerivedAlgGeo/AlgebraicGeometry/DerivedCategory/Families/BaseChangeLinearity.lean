/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeAdjunction

/-!
# Linearity and the projection formula for K-flat base change

This file states the two compatibility isomorphisms needed for linearity of base-change functors,
using the actual K-flat derived tensors and derived pullback/pushforward interfaces constructed in
the preceding files.

The pullback tensorator says that pulling back after tensoring agrees with tensoring the two
pullbacks. The projection formula says that pushing forward after tensoring by a pulled-back object
agrees with tensoring the pushforward. These are geometric proof obligations rather than new
functor slots.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}

namespace KFlatBaseChangeData

/-- The K-flat derived tensor on the fibre product underlying a base-change datum. -/
noncomputable def derivedTensor (D : KFlatBaseChangeData X T) :
    Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left ⥤
        Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left :=
  D.tensorResolution.derivedTensorToDqc
    (D.tensorResolution.preservesQuasicoherentCohomology_of_resolvedTensor
      D.tensorQuasicoherent)

@[simp]
theorem derivedTensor_obj_obj_obj (D : KFlatBaseChangeData X T)
    (E F : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) :
    (((D.derivedTensor.obj E).obj F).obj) =
      ((D.tensorResolution.derivedTensor.obj E.obj).obj F.obj) :=
  rfl

/-- Linearity of derived pullback with respect to the constructed K-flat tensors. For each twist
`B`, this is the natural isomorphism
`(B ⊗ -) ⋙ Lf^* ≅ Lf^* ⋙ (Lf^* B ⊗ -)`. -/
structure PullbackTensorCompatibility
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f)) where
  /-- Pullback commutes with left tensor twists. -/
  iso (B : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ U).left) :
    (DU.derivedTensor.obj B) ⋙ pull.functor ≅
      pull.functor ⋙ (DT.derivedTensor.obj (pull.functor.obj B))

/-- The projection formula for the actual K-flat tensors and derived pullback/pushforward:
`Rf_*(Lf^* B ⊗ A) ≅ B ⊗ Rf_* A`, naturally in `A`. -/
structure ProjectionFormula
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f)) where
  /-- The projection-formula isomorphism for each target twist. -/
  iso (B : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ U).left) :
    (DT.derivedTensor.obj (pull.functor.obj B)) ⋙ push.functor ≅
      push.functor ⋙ (DU.derivedTensor.obj B)

/-- A derived pullback preserves a component after twisting when the corresponding K-flat tensor
endofunctor maps that component to itself. -/
def TensorPreservesQuasicoherentComponent
    (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (B : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) : Prop :=
  D.quasicoherentComponent P ≤
    (D.quasicoherentComponent P).inverseImage (D.derivedTensor.obj B)

/-- Tensor by `B` restricted to the constructed quasicoherent base-change component. -/
noncomputable def quasicoherentTensor
    (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (B : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (hB : D.TensorPreservesQuasicoherentComponent P B) :
    D.QuasicoherentCategory P ⥤ D.QuasicoherentCategory P :=
  ObjectProperty.liftOfLE (D.derivedTensor.obj B) hB

/-- Forgetting component witnesses recovers tensor by `B` on `Dqc`. -/
noncomputable def quasicoherentTensorCompInclusion
    (D : KFlatBaseChangeData X T)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (B : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (hB : D.TensorPreservesQuasicoherentComponent P B) :
    D.quasicoherentTensor P B hB ⋙ (D.quasicoherentComponent P).ι ≅
      (D.quasicoherentComponent P).ι ⋙ D.derivedTensor.obj B :=
  (D.quasicoherentComponent P).liftCompιIso
    ((D.quasicoherentComponent P).ι ⋙ D.derivedTensor.obj B)
    (fun E ↦ hB E.obj E.property)

/-- Pullback tensor compatibility restricted to the constructed quasicoherent base-change
components. This is the linearity isomorphism for pullback. -/
noncomputable def quasicoherentPullbackTensorIso
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hPull : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hTensor : PullbackTensorCompatibility DT DU pull)
    (B : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ U).left)
    (hBU : DU.TensorPreservesQuasicoherentComponent P B)
    (hBT : DT.TensorPreservesQuasicoherentComponent P (pull.functor.obj B)) :
    DU.quasicoherentTensor P B hBU ⋙
        quasicoherentPullback DT DU P pull hPull ≅
      quasicoherentPullback DT DU P pull hPull ⋙
        DT.quasicoherentTensor P (pull.functor.obj B) hBT :=
  Functor.fullyFaithfulCancelRight (DT.quasicoherentComponent P).ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (DU.quasicoherentTensor P B hBU)
        (quasicoherentPullbackCompInclusion DT DU P pull hPull) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (DU.quasicoherentTensorCompInclusion P B hBU) pull.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (DU.quasicoherentComponent P).ι (hTensor.iso B) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (quasicoherentPullbackCompInclusion DT DU P pull hPull).symm
        (DT.derivedTensor.obj (pull.functor.obj B)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (quasicoherentPullback DT DU P pull hPull)
        (DT.quasicoherentTensorCompInclusion P (pull.functor.obj B) hBT).symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The projection formula restricted to the constructed quasicoherent base-change components.
This is the linearity isomorphism for pushforward. -/
noncomputable def quasicoherentProjectionFormulaIso
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (hPush : PushforwardPreservesQuasicoherentComponent DT DU P push)
    (hProjection : ProjectionFormula DT DU pull push)
    (B : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ U).left)
    (hBT : DT.TensorPreservesQuasicoherentComponent P (pull.functor.obj B))
    (hBU : DU.TensorPreservesQuasicoherentComponent P B) :
    DT.quasicoherentTensor P (pull.functor.obj B) hBT ⋙
        quasicoherentPushforward DT DU P push hPush ≅
      quasicoherentPushforward DT DU P push hPush ⋙
        DU.quasicoherentTensor P B hBU :=
  Functor.fullyFaithfulCancelRight (DU.quasicoherentComponent P).ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (DT.quasicoherentTensor P (pull.functor.obj B) hBT)
        (quasicoherentPushforwardCompInclusion DT DU P push hPush) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (DT.quasicoherentTensorCompInclusion P (pull.functor.obj B) hBT) push.functor ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (DT.quasicoherentComponent P).ι (hProjection.iso B) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (quasicoherentPushforwardCompInclusion DT DU P push hPush).symm
        (DU.derivedTensor.obj B) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (quasicoherentPushforward DT DU P push hPush)
        (DU.quasicoherentTensorCompInclusion P B hBU).symm ≪≫
      (Functor.associator _ _ _).symm)

end KFlatBaseChangeData

end


end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
