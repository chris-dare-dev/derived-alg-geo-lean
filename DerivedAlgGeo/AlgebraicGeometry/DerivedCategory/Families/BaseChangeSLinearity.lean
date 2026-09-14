/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeTensorProjectionFormula

/-!
# Base-scheme linearity for external-product semiorthogonality

This file refines the source tensor-closure hypothesis used by the
first-projection formula to the `S`-linearity appearing in Proposition 3.15.
It exposes both levels of the base action:

* compact objects of `Dqc(S)`, modeling the original `Perf(S)`-linear
  decomposition; and
* arbitrary objects of `Dqc(S)`, modeling its presentable quasicoherent
  extension.

Both act on `Dqc(X)` by genuine derived pullback along `X → S`, followed by
the K-flat source tensor. A projection coefficient pulled back from the
corresponding level on the base then gives the coefficient-local closure
required by the semiorthogonality argument.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]

/-- The identity scheme over `S`, used as the terminal base-change object. -/
abbrev identityBaseChange (S : Scheme.{u}) : SchemeBaseChange S :=
  Over.mk (𝟙 S)

/-- The structure morphism `X → S`, regarded as a morphism in `Over S` to
the identity base change. -/
def toIdentityBaseChange (X : SchemeBaseChange S) :
    X ⟶ identityBaseChange S :=
  Over.homMk X.hom (Category.comp_id _)

/-- The quasicoherent derived category of the base scheme. -/
abbrev BaseDqc (S : Scheme.{u}) :=
  Dqc.SchemeQuasicoherentDerivedCategory S

/-- The compact objects of `Dqc(S)`, modeling `Perf(S)` in this layer. -/
abbrev CompactBaseDqc (S : Scheme.{u}) :=
  (ObjectProperty.compactObjects.{u} (C := BaseDqc S)).FullSubcategory

namespace KFlatBaseChangeData

namespace SourceTensorData

/-- For a fixed source object, the base-variable action functor: pull back
from `S` to `X`, then tensor on the right. -/
noncomputable def dqcBaseActionInBase
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (F : SourceDqc X) : BaseDqc S ⥤ SourceDqc X :=
  pullBase.functor ⋙ Q.derivedTensor.obj F

@[simp]
theorem dqcBaseActionInBase_obj
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (F : SourceDqc X) (B : BaseDqc S) :
    (dqcBaseActionInBase (D := D) Q pullBase F).obj B =
      (Q.derivedTensor.obj F).obj (pullBase.functor.obj B) :=
  rfl

/-- The action of an arbitrary quasicoherent base object on `Dqc(X)`: pull
it back along `X → S`, then tensor by it on the right. -/
noncomputable def dqcBaseAction
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (B : BaseDqc S) : SourceDqc X ⥤ SourceDqc X :=
  Q.derivedTensor.flip.obj (pullBase.functor.obj B)

@[simp]
theorem dqcBaseAction_obj
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (B : BaseDqc S) (F : SourceDqc X) :
    (dqcBaseAction (D := D) Q pullBase B).obj F =
      (Q.derivedTensor.obj F).obj (pullBase.functor.obj B) :=
  rfl

/-- The action of a compact base object on `Dqc(X)`: pull it back along
`X → S`, then tensor by it on the right. -/
noncomputable def baseAction
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (B : CompactBaseDqc S) : SourceDqc X ⥤ SourceDqc X :=
  Q.derivedTensor.flip.obj (pullBase.functor.obj B.obj)

@[simp]
theorem baseAction_obj
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (B : CompactBaseDqc S) (F : SourceDqc X) :
    (baseAction (D := D) Q pullBase B).obj F =
      (Q.derivedTensor.obj F).obj (pullBase.functor.obj B.obj) :=
  rfl

/-- Paper-level `S`-linearity of the source semiorthogonal sequence: every
component is preserved by the action of every compact object of `Dqc(S)`. -/
def SLinearComponents
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (A : SemiorthogonalSequence (SourceDqc X) ι) : Prop :=
  ∀ ⦃j : ι⦄ (F : SourceDqc X), A.component j F →
    ∀ B : CompactBaseDqc S,
      A.component j ((baseAction (D := D) Q pullBase B).obj F)

/-- `Dqc(S)`-linearity of the quasicoherent source components. This is the
presentable extension of `S`-linearity used when a projection coefficient on
the base is quasicoherent but not necessarily compact. -/
def DqcSLinearComponents
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (A : SemiorthogonalSequence (SourceDqc X) ι) : Prop :=
  ∀ ⦃j : ι⦄ (F : SourceDqc X), A.component j F →
    ∀ B : BaseDqc S,
      A.component j ((dqcBaseAction (D := D) Q pullBase B).obj F)

/-- Presentability data needed to extend the compact base action to all of
`Dqc(S)`.

The base is generated from compact objects by coproducts and extensions, and
for each fixed source object the action in the base variable is exact and
preserves the relevant small coproducts. -/
structure PresentableBaseActionData
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X)) where
  /-- Compact objects generate `Dqc(S)` under coproducts and extensions. -/
  baseGenerated :
    (ObjectProperty.compactObjects.{u} (C := BaseDqc S)).coprodClosure.{u} = ⊤
  /-- The action in the base variable commutes with shifts. -/
  actionCommShift (F : SourceDqc X) :
    (dqcBaseActionInBase (D := D) Q pullBase F).CommShift ℤ
  /-- The action in the base variable is triangulated. -/
  actionTriangulated (F : SourceDqc X) :
    (dqcBaseActionInBase (D := D) Q pullBase F).IsTriangulated
  /-- The action in the base variable preserves scheme-universe coproducts. -/
  actionCocontinuous (F : SourceDqc X) :
    (dqcBaseActionInBase (D := D) Q pullBase F).PreservesSmallCoproducts.{u}

namespace PresentableBaseActionData

/-- Perf(S)-linearity extends to Dqc(S)-linearity when compact objects
generate the base and the base action preserves triangles and coproducts. -/
theorem dqcSLinearComponents
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (G : PresentableBaseActionData (D := D) Q pullBase)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (hCoprod : ∀ j (κ : Type u),
      (A.component j).IsClosedUnderColimitsOfShape (Discrete κ))
    (hS : SLinearComponents (D := D) Q pullBase A) :
    DqcSLinearComponents (D := D) Q pullBase A := by
  intro j F hF B
  let action := dqcBaseActionInBase (D := D) Q pullBase F
  letI : action.CommShift ℤ := G.actionCommShift F
  letI : action.IsTriangulated := G.actionTriangulated F
  letI : (A.component j).IsTriangulated := hA j
  letI : (A.component j).IsClosedUnderIsomorphisms := hIso j
  letI (κ : Type u) :
      (A.component j).IsClosedUnderColimitsOfShape (Discrete κ) :=
    hCoprod j κ
  have hB :
      (ObjectProperty.compactObjects.{u} (C := BaseDqc S)).coprodClosure.{u} B := by
    rw [G.baseGenerated]
    trivial
  have hMap :=
    (ObjectProperty.compactObjects.{u} (C := BaseDqc S)).coprodClosure_map_obj
      action (G.actionCocontinuous F) hB
  change A.component j (action.obj B)
  exact ((ObjectProperty.compactObjects.{u} (C := BaseDqc S)).map action).coprodClosure_le
    (Q := A.component j) (fun E hE ↦ by
      rcases hE with ⟨C, hC, ⟨e⟩⟩
      exact (A.component j).prop_of_iso e
        (by simpa [action, dqcBaseActionInBase, dqcBaseAction] using
          hS F hF (⟨C, hC⟩ : CompactBaseDqc S))) _ hMap

end PresentableBaseActionData

end SourceTensorData

namespace CompactFiberProjectionFormula

/-- Evidence that all source coefficients in a compact-fibre projection
formula come by derived pullback from compact objects on the base scheme. -/
structure BaseCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X)) where
  /-- The compact object on `S` representing each source coefficient. -/
  baseCoefficient :
    CompactDqcFiber T → CompactDqcFiber T → ℤ → ℤ → CompactBaseDqc S
  /-- The projection coefficient is the pullback of its representing base
  object. -/
  coefficientIso (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    P.coefficient Gi Gj a b ≅
      pullBase.functor.obj (baseCoefficient Gi Gj a b).obj

/-- Evidence that all projection-formula coefficients are pulled back from
quasicoherent objects on the base. Unlike `BaseCoefficientData`, this does
not require those objects to be compact. -/
structure DqcBaseCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X)) where
  /-- The quasicoherent object on `S` representing each coefficient. -/
  baseCoefficient :
    CompactDqcFiber T → CompactDqcFiber T → ℤ → ℤ → BaseDqc S
  /-- The projection coefficient is the pullback of its representing base
  object. -/
  coefficientIso (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    P.coefficient Gi Gj a b ≅
      pullBase.functor.obj (baseCoefficient Gi Gj a b)

namespace BaseCoefficientData

/-- Compact base coefficients can be forgotten to quasicoherent base
coefficients. -/
def toDqc
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    {P : D.CompactFiberProjectionFormula H Q pushFst}
    {pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X)}
    (C : BaseCoefficientData (D := D) P pullBase) :
    DqcBaseCoefficientData (D := D) P pullBase where
  baseCoefficient Gi Gj a b := (C.baseCoefficient Gi Gj a b).obj
  coefficientIso Gi Gj a b := C.coefficientIso Gi Gj a b

end BaseCoefficientData

/-- Base coefficients and `S`-linearity imply the coefficient-local source
component preservation required by the projection formula. -/
theorem preservesSourceComponents_of_sLinear
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (C : BaseCoefficientData (D := D) P pullBase)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (hS : SourceTensorData.SLinearComponents
      (D := D) Q pullBase A) :
    PreservesSourceComponents (D := D) P A := by
  intro j Fj Gi Gj a b
  letI : (A.component j).IsClosedUnderIsomorphisms := hIso j
  exact (A.component j).prop_of_iso
    ((Q.derivedTensor.obj Fj.obj).mapIso
      (C.coefficientIso Gi Gj a b)).symm
    (hS Fj.obj Fj.property.1 (C.baseCoefficient Gi Gj a b))

/-- Quasicoherent base coefficients and `Dqc(S)`-linearity imply the exact
coefficient-local preservation required by the projection formula. -/
theorem preservesSourceComponents_of_dqcSLinear
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (C : DqcBaseCoefficientData (D := D) P pullBase)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (hS : SourceTensorData.DqcSLinearComponents
      (D := D) Q pullBase A) :
    PreservesSourceComponents (D := D) P A := by
  intro j Fj Gi Gj a b
  letI : (A.component j).IsClosedUnderIsomorphisms := hIso j
  exact (A.component j).prop_of_iso
    ((Q.derivedTensor.obj Fj.obj).mapIso
      (C.coefficientIso Gi Gj a b)).symm
    (hS Fj.obj Fj.property.1 (C.baseCoefficient Gi Gj a b))

end CompactFiberProjectionFormula

/-- Compact-fibre duality, a first-projection formula with base coefficients,
and `S`-linearity of the source sequence prove perfect-component
semiorthogonality after base change. -/
theorem perfectComponentsSemiorthogonal_of_projectionFormula_of_sLinear
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (C : CompactFiberProjectionFormula.BaseCoefficientData
      (D := D) P pullBase)
    (hS : SourceTensorData.SLinearComponents
      (D := D) Q pullBase A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_projectionFormula A hA hIso H Q
    pushFst adj P
    (CompactFiberProjectionFormula.preservesSourceComponents_of_sLinear
      (D := D) P pullBase C A hIso hS)

/-- Compact-fibre duality, a first-projection formula with quasicoherent base
coefficients, and `Dqc(S)`-linearity of the source sequence prove
perfect-component semiorthogonality after base change. -/
theorem perfectComponentsSemiorthogonal_of_projectionFormula_of_dqcSLinear
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (pullBase : DqcLeftDerivedPullback (toIdentityBaseChange X))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (C : CompactFiberProjectionFormula.DqcBaseCoefficientData
      (D := D) P pullBase)
    (hS : SourceTensorData.DqcSLinearComponents
      (D := D) Q pullBase A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_projectionFormula A hA hIso H Q
    pushFst adj P
    (CompactFiberProjectionFormula.preservesSourceComponents_of_dqcSLinear
      (D := D) P pullBase C A hIso hS)

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
