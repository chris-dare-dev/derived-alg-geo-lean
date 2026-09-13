/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.QuasiEquivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionCotwistComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionTwistComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctor

/-!
# Kernel autoequivalences from enhanced twist/cotwist conditions

`SphericalTwist.TwistCotwistEquivalenceConditions` records that the dg twist
and the unshifted dg cotwist cone of an `EnhancedAdjunctionCones` package are
quasi-equivalences.  The Fourier--Mukai comparison layer asks for the weaker
consequences that their `H⁰` functors are equivalences before packaging the
selected kernels as `KernelAutoequivalence`s.

This file is the adapter between those canonical interfaces.  It specializes
the existing twist and cotwist kernel constructors to the corresponding cone
fields and obtains their equivalence hypotheses from the recorded
quasi-equivalences.  The twist and cotwist remain independent declarations:
their endocorrespondences, kernel categories, enhancements, and convolution
data need not agree, so no paired kernel record is introduced.

The conditions alone provide ordinary equivalences, not compatible target
shift structures.  The exactness wrappers therefore continue to require the
existing Fourier--Mukai `ShiftCompatibility` inputs and triangulated endpoint
presentations.  No dual-twist or dual-cotwist equivalence, inverse-kernel
formula, dg quasi-equivalence of a Fourier--Mukai transform, or sphericality
is inferred.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY v₁ v₂ vW vE uA uB uX uY u₁ u₂ uW uE

namespace CategoryTheory.Triangulated.SphericalTwist

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated FourierMukai

namespace TwistCotwistEquivalenceConditions

/-! ### Twist kernel -/

section Twist

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W₁ : Type u₁} {W₂ : Type u₂} {W : Type uW}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{v₁} W₁] [Category.{v₂} W₂] [Category.{vW} W]
  {S : DGFunctor A B} {L R : DGFunctor B A}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}
  [IsPretriangulated B]
  [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [eB.functor.CommShift ℤ]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ]
  {cones : EnhancedAdjunctionCones S L R}

open CounitKernelConeData.PresentedCounitComparisonData

/-- The selected Fourier--Mukai twist kernel is an autoequivalence under the
canonical enhanced twist/cotwist equivalence conditions. -/
@[reducible]
noncomputable def twistKernelAutoequivalence
    (h : TwistCotwistEquivalenceConditions cones)
    (H : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform P) (C'.transform Q))
    (T : CounitKernelConeData C C' E e P
      (RightAdjointKernelData.ofH0Presentation H cones.rightAdj) D U)
    (hE : E.KernelEvaluationExact)
    (N : T.PresentedCounitComparisonData cones.rightAdj H cones.twist hE) :
    KernelAutoequivalence Y W :=
  CounitKernelConeData.PresentedCounitComparisonData.twistKernelAutoequivalence
    cones.rightAdj H cones.twist T hE N
      (cones.twistFunctor.isEquivalence_h0 h.twist)

set_option backward.isDefEq.respectTransparency false in
/-- The selected twist kernel autoequivalence is exact when the existing
Fourier--Mukai comparison respects the selected target shift structure. -/
theorem twistKernelAutoequivalenceIsTriangulated
    [eB.functor.IsTriangulated]
    (h : TwistCotwistEquivalenceConditions cones)
    (H : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform P) (C'.transform Q))
    (T : CounitKernelConeData C C' E e P
      (RightAdjointKernelData.ofH0Presentation H cones.rightAdj) D U)
    (hE : E.KernelEvaluationExact)
    (N : T.PresentedCounitComparisonData cones.rightAdj H cones.twist hE)
    (hN : N.ShiftCompatibility) :
    letI : (twistKernelAutoequivalence h H T hE N).equiv.functor.CommShift ℤ :=
      hN.twistCommShift
    letI : (twistKernelAutoequivalence h H T hE N).equiv.inverse.CommShift ℤ :=
      (twistKernelAutoequivalence h H T hE N).equiv.commShiftInverse ℤ
    letI : (twistKernelAutoequivalence h H T hE N).equiv.CommShift ℤ :=
      (twistKernelAutoequivalence h H T hE N).equiv.commShift_of_functor ℤ
    (twistKernelAutoequivalence h H T hE N).equiv.IsTriangulated :=
  ShiftCompatibility.twistKernelAutoequivalenceIsTriangulated
    cones.rightAdj H cones.twist T hE N hN
      (cones.twistFunctor.isEquivalence_h0 h.twist)

end Twist

/-! ### Cotwist kernel -/

section Cotwist

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W₁ : Type u₁} {W₂ : Type u₂} {W : Type uW}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{v₁} W₁] [Category.{v₂} W₂] [Category.{vW} W]
  {S : DGFunctor A B} {L R : DGFunctor B A}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence X X W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}
  [IsPretriangulated A]
  [Limits.HasZeroObject X] [HasShift X ℤ] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eA.functor.CommShift ℤ]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ]
  {cones : EnhancedAdjunctionCones S L R}

open AdjunctionUnitKernelConeData.PresentedUnitComparisonData

/-- The selected shifted Fourier--Mukai cotwist kernel is an autoequivalence
under the canonical enhanced twist/cotwist equivalence conditions. -/
@[reducible]
noncomputable def cotwistKernelAutoequivalence
    (h : TwistCotwistEquivalenceConditions cones)
    (H : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform P) (C'.transform Q))
    (T : AdjunctionUnitKernelConeData C C' E e P
      (RightAdjointKernelData.ofH0Presentation H cones.rightAdj) D U)
    (hE : E.KernelEvaluationExact)
    (N : T.PresentedUnitComparisonData cones.rightAdj H cones.cotwistCone hE) :
    KernelAutoequivalence X W :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.cotwistKernelAutoequivalence
    cones.rightAdj H cones.cotwistCone T hE N
      (cones.cotwistConeFunctor.isEquivalence_h0 h.cotwist)

set_option backward.isDefEq.respectTransparency false in
/-- The selected cotwist kernel autoequivalence is exact when the existing
Fourier--Mukai comparison respects the selected target shift structure. -/
theorem cotwistKernelAutoequivalenceIsTriangulated
    [eA.functor.IsTriangulated]
    (h : TwistCotwistEquivalenceConditions cones)
    (H : DGAdjunction.H0Presentation (L := S) (R := R) eA eB
      (C.transform P) (C'.transform Q))
    (T : AdjunctionUnitKernelConeData C C' E e P
      (RightAdjointKernelData.ofH0Presentation H cones.rightAdj) D U)
    (hE : E.KernelEvaluationExact)
    (N : T.PresentedUnitComparisonData cones.rightAdj H cones.cotwistCone hE)
    (hN : N.ShiftCompatibility) :
    letI : (cotwistKernelAutoequivalence h H T hE N).equiv.functor.CommShift ℤ :=
      hN.cotwistCommShift
    letI : (cotwistKernelAutoequivalence h H T hE N).equiv.inverse.CommShift ℤ :=
      (cotwistKernelAutoequivalence h H T hE N).equiv.commShiftInverse ℤ
    letI : (cotwistKernelAutoequivalence h H T hE N).equiv.CommShift ℤ :=
      (cotwistKernelAutoequivalence h H T hE N).equiv.commShift_of_functor ℤ
    (cotwistKernelAutoequivalence h H T hE N).equiv.IsTriangulated :=
  ShiftCompatibility.cotwistKernelAutoequivalenceIsTriangulated
    cones.rightAdj H cones.cotwistCone T hE N hN
      (cones.cotwistConeFunctor.isEquivalence_h0 h.cotwist)

end Cotwist

end TwistCotwistEquivalenceConditions

end CategoryTheory.Triangulated.SphericalTwist
