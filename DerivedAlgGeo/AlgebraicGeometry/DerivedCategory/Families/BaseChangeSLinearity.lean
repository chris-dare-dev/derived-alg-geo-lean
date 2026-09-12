/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeTensorProjectionFormula

/-!
# Base-scheme linearity for external-product semiorthogonality

This file refines the source tensor-closure hypothesis used by the
first-projection formula to the `S`-linearity appearing in Proposition 3.15.
The acting objects are compact objects of `Dqc(S)`. They act on `Dqc(X)` by
genuine derived pullback along `X → S`, followed by the K-flat source tensor.

If every coefficient produced by the first-projection formula is isomorphic
to a pulled-back compact base object, `S`-linearity of the source components
implies the coefficient-local closure required by the semiorthogonality
argument.
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

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
