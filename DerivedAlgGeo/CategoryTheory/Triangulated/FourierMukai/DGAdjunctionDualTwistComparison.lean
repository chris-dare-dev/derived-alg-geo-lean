/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionCotwistComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DualTwistKernel

/-!
# Comparing presented dg and Fourier--Mukai dual twists

Let `L ⊣ S` be a strict dg adjunction whose `H⁰` presentation identifies
`S` with a Fourier--Mukai transform and `L` with a kernel-presented left
adjoint.  The dg unit cone and an independently chosen enhanced kernel cone
then produce two presentations of the dual twist of `S`.

This file is the semantic left-adjunction facade for the existing cotwist
comparison.  It swaps the two endpoint categories and correspondences, then
reuses `AdjunctionUnitKernelConeData` through the definitional conversion
`LeftAdjointKernelData.toRightAdjointKernelData`.  In particular, it does not
introduce a second comparison record or a second shift package.  The
conventional dual twist is the pointwise `[-1]` shift of the unit cone, exactly
as in `DualTwistKernelConeData`.

The objectwise comparisons remain noncanonical.  Natural comparison data,
equivalence of `H⁰` of the unshifted dg unit cone, and shift compatibility are
all explicit inputs.  Nothing here constructs those inputs, identifies an
inverse kernel, upgrades the dg functor to a quasi-equivalence, or asserts
sphericality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY v₁ v₂ vW vE uA uB uX uY u₁ u₂ uW uE

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory DGCategoryStruct DGCategory Pretriangulated

variable {A : Type uA} {B : Type uB} {X : Type uX} {Y : Type uY}
  {W₁ : Type u₁} {W₂ : Type u₂} {W : Type uW}
  [DGCategory.{v} A] [DGCategory.{v} B]
  [Category.{vX} X] [Category.{vY} Y]
  [Category.{v₁} W₁] [Category.{v₂} W₂] [Category.{vW} W]
  {L : DGFunctor B A} {S : DGFunctor A B}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}

namespace DualTwistKernelConeData

variable [IsPretriangulated B]
  [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [eB.functor.CommShift ℤ]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ]
  (adj : DGAdjunction L S)
  (H : DGAdjunction.H0Presentation (L := L) (R := S) eB eA
    (C'.transform Q) (C.transform P))
  (K : adj.UnitConeData)
  (T : DualTwistKernelConeData C C' E e P
    (LeftAdjointKernelData.ofH0Presentation H adj) D U)
  (hE : E.KernelEvaluationExact)

section Pointwise

variable [eB.functor.IsTriangulated] [e.equiv.functor.IsTriangulated]

/-- At each target object, the presented dg left-unit triangle is
noncanonically isomorphic to the selected Fourier--Mukai left-unit triangle. -/
noncomputable abbrev presentedLeftUnitTriangleObjIso (Z : Y) :
    (H.presentedUnitTriangle K).obj Z ≅
      (T.unitTriangleInTarget hE).obj Z :=
  AdjunctionUnitKernelConeData.presentedUnitTriangleObjIso adj H K T hE Z

/-- The resulting noncanonical objectwise comparison of the unshifted dg and
Fourier--Mukai left-unit cones. -/
noncomputable abbrev transportedDualTwistConeObjIso (Z : Y) :
    (K.transportedUnitCone eB).obj Z ≅ T.dualTwistCone.obj Z :=
  AdjunctionUnitKernelConeData.transportedUnitConeObjIso adj H K T hE Z

/-- Inverse rotation gives the noncanonical objectwise comparison of the
conventional dual-twist triangles. -/
noncomputable abbrev presentedDualTwistTriangleObjIso (Z : Y) :
    (H.presentedCotwistTriangle K).obj Z ≅
      (T.dualTwistTriangleInTarget hE).obj Z :=
  AdjunctionUnitKernelConeData.presentedCotwistTriangleObjIso adj H K T hE Z

/-- The resulting objectwise comparison from the conventional transported dg
dual twist to the Fourier--Mukai dual twist. -/
noncomputable abbrev transportedDualTwistObjIso (Z : Y) :
    (K.transportedCotwist eB).obj Z ≅ T.dualTwist.obj Z :=
  AdjunctionUnitKernelConeData.transportedCotwistObjIso adj H K T hE Z

/-- The actual shifted dg unit cone is noncanonically objectwise isomorphic to
the selected Fourier--Mukai dual twist. -/
noncomputable abbrev transportedDGDualTwistObjIso (Z : Y) :
    (K.transportedDGCotwist eB).obj Z ≅ T.dualTwist.obj Z :=
  AdjunctionUnitKernelConeData.transportedDGCotwistObjIso adj H K T hE Z

end Pointwise

/-! ### Supplied natural comparison data -/

/-- Natural comparison data for the presented dg and Fourier--Mukai dual
twists.  This is the existing unit/cotwist comparison after swapping the two
endpoints; no parallel record is introduced. -/
abbrev PresentedDualTwistComparisonData :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData adj H K T hE

namespace PresentedDualTwistComparisonData

/-- Supply a natural comparison of the unshifted left-unit cones and the two
triangle-map squares not fixed by the common unit. -/
def ofConeIso
    (iso : K.transportedUnitCone eB ≅ T.dualTwistCone)
    (second : H.compositeToTransportedUnitCone K ≫ iso.hom =
      T.compositeToDualTwistCone hE)
    (third : H.transportedUnitConeToShiftedIdentity K =
      iso.hom ≫ T.dualTwistConeToShiftedIdentity hE) :
    T.PresentedDualTwistComparisonData adj H K hE :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.ofConeIso
    adj H K T hE iso second third

section Comparison

variable (N : T.PresentedDualTwistComparisonData adj H K hE)

/-- The supplied data give a natural comparison of the two left-unit triangle
families. -/
noncomputable abbrev presentedLeftUnitTriangleIso :
    H.presentedUnitTriangle K ≅ T.unitTriangleInTarget hE :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.presentedUnitTriangleIso
    adj H K T hE N

/-- The supplied natural isomorphism of the unshifted left-unit cones. -/
noncomputable abbrev transportedDualTwistConeIso :
    K.transportedUnitCone eB ≅ T.dualTwistCone :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.transportedUnitConeIso
    adj H K T hE N

/-- Inverse rotation gives a natural comparison of the conventional
dual-twist triangle families. -/
noncomputable abbrev presentedDualTwistTriangleIso :
    H.presentedCotwistTriangle K ≅ T.dualTwistTriangleInTarget hE :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.presentedCotwistTriangleIso
    adj H K T hE N

/-- The induced natural isomorphism from the conventional transported dg dual
twist to the selected Fourier--Mukai dual twist. -/
noncomputable abbrev transportedDualTwistIso :
    K.transportedCotwist eB ≅ T.dualTwist :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.transportedCotwistIso
    adj H K T hE N

/-- The transport of the actual shifted dg unit cone is naturally isomorphic
to the selected Fourier--Mukai dual twist. -/
noncomputable abbrev transportedDGDualTwistIso :
    K.transportedDGCotwist eB ≅ T.dualTwist :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.transportedDGCotwistIso
    adj H K T hE N

end Comparison

/-- The conventional transported dg dual twist is a kernel functor through
the supplied natural comparison. -/
theorem transportedDualTwist_isKernelFunctor
    (N : T.PresentedDualTwistComparisonData adj H K hE) :
    E.IsKernelFunctor (K.transportedCotwist eB) :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.transportedCotwist_isKernelFunctor
    adj H K T hE N

/-- The actual shifted dg unit cone is a kernel functor through the composite
natural comparison. -/
theorem transportedDGDualTwist_isKernelFunctor
    (N : T.PresentedDualTwistComparisonData adj H K hE) :
    E.IsKernelFunctor (K.transportedDGCotwist eB) :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.transportedDGCotwist_isKernelFunctor
    adj H K T hE N

/-- An explicit equivalence hypothesis on `H⁰` of the unshifted dg unit cone
transfers to the selected Fourier--Mukai dual twist. -/
theorem dualTwist_isEquivalence
    (N : T.PresentedDualTwistComparisonData adj H K hE)
    (hK : K.unitCone.h0.IsEquivalence) :
    T.dualTwist.IsEquivalence :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.cotwist_isEquivalence
    adj H K T hE N hK

/-- The selected shifted dual-twist kernel, packaged as a kernel
autoequivalence under the explicit `H⁰` equivalence hypothesis. -/
noncomputable abbrev dualTwistKernelAutoequivalence
    (N : T.PresentedDualTwistComparisonData adj H K hE)
    (hK : K.unitCone.h0.IsEquivalence) : KernelAutoequivalence Y W :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.cotwistKernelAutoequivalence
    adj H K T hE N hK

/-! ### Compatibility with selected shift structures -/

variable (N : T.PresentedDualTwistComparisonData adj H K hE)

/-- Shift compatibility for the dg/Fourier--Mukai dual-twist comparison.  This
is a semantic alias of the existing cotwist package, not a second structure. -/
abbrev ShiftCompatibility :=
  AdjunctionUnitKernelConeData.PresentedUnitComparisonData.ShiftCompatibility
    adj H K T hE N

namespace ShiftCompatibility

open AdjunctionUnitKernelConeData.PresentedUnitComparisonData.ShiftCompatibility

/-- Supply the selected Fourier--Mukai dual-twist shift structure and
compatibility of the conventional comparison.  The result is the existing
cotwist compatibility record viewed through the semantic facade. -/
def ofCommShift
    (dualTwistCommShift : T.dualTwist.CommShift ℤ)
    (transportedDualTwistIso_commShift :
      letI : (K.transportedCotwist eB).CommShift ℤ :=
        K.transportedCotwistCommShift (eC := eB)
      letI : T.dualTwist.CommShift ℤ := dualTwistCommShift
      NatTrans.CommShift N.transportedDualTwistIso.hom ℤ) :
    N.ShiftCompatibility where
  cotwistCommShift := dualTwistCommShift
  transportedCotwistIso_commShift := transportedDualTwistIso_commShift

variable (h : N.ShiftCompatibility)

/-- The selected shift structure on the Fourier--Mukai dual twist. -/
abbrev dualTwistCommShift : T.dualTwist.CommShift ℤ :=
  h.cotwistCommShift

/-- The conventional dual-twist comparison respects the canonical source
shift package and the selected Fourier--Mukai shift package. -/
theorem transportedDualTwistIso_commShift :
    letI : (K.transportedCotwist eB).CommShift ℤ :=
      K.transportedCotwistCommShift (eC := eB)
    letI : T.dualTwist.CommShift ℤ := h.dualTwistCommShift
    NatTrans.CommShift N.transportedDualTwistIso.hom ℤ :=
  h.transportedCotwistIso_commShift

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from the actual shifted dg unit cone respects the canonical
source shift package and the selected Fourier--Mukai shift package. -/
theorem transportedDGDualTwistIso_commShift [eB.functor.Additive] :
    letI : (K.transportedDGCotwist eB).CommShift ℤ :=
      (K.unitCone.shiftedFunctor (-1 : ℤ)).transportedH0CommShift
    letI : T.dualTwist.CommShift ℤ := h.dualTwistCommShift
    NatTrans.CommShift N.transportedDGDualTwistIso.hom ℤ :=
  transportedDGCotwistIso_commShift adj H K T hE N h

set_option backward.isDefEq.respectTransparency false in
/-- The selected Fourier--Mukai dual twist is triangulated when the comparison
respects shifts and the endpoint presentation equivalence is triangulated. -/
theorem dualTwistIsTriangulated [eB.functor.IsTriangulated] :
    letI : T.dualTwist.CommShift ℤ := h.dualTwistCommShift
    T.dualTwist.IsTriangulated :=
  cotwistIsTriangulated adj H K T hE N h

set_option backward.isDefEq.respectTransparency false in
/-- The selected dual-twist kernel autoequivalence is exact relative to the
selected target shift package. -/
theorem dualTwistKernelAutoequivalenceIsTriangulated
    [eB.functor.IsTriangulated] (hK : K.unitCone.h0.IsEquivalence) :
    letI : (dualTwistKernelAutoequivalence adj H K T hE N hK).equiv.functor.CommShift ℤ :=
      h.dualTwistCommShift
    letI : (dualTwistKernelAutoequivalence adj H K T hE N hK).equiv.inverse.CommShift ℤ :=
      (dualTwistKernelAutoequivalence adj H K T hE N hK).equiv.commShiftInverse ℤ
    letI : (dualTwistKernelAutoequivalence adj H K T hE N hK).equiv.CommShift ℤ :=
      (dualTwistKernelAutoequivalence adj H K T hE N hK).equiv.commShift_of_functor ℤ
    (dualTwistKernelAutoequivalence adj H K T hE N hK).equiv.IsTriangulated :=
  cotwistKernelAutoequivalenceIsTriangulated adj H K T hE N h hK

end ShiftCompatibility

end PresentedDualTwistComparisonData

end DualTwistKernelConeData

end CategoryTheory.Triangulated.FourierMukai
