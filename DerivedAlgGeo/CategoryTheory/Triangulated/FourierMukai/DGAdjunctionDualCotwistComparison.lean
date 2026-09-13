/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionTwistComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DualCotwistKernel

/-!
# Comparing presented dg and Fourier--Mukai dual cotwists

Let `L ⊣ S` be a strict dg adjunction whose `H⁰` presentation identifies
`S` with a Fourier--Mukai transform and `L` with a kernel-presented left
adjoint.  The dg counit cone and an independently chosen enhanced kernel cone
then produce two presentations of the dual cotwist of `S`.

This file is the semantic left-adjunction facade for the existing twist
comparison.  It swaps the two endpoint categories and correspondences, then
reuses `CounitKernelConeData` through the definitional conversion
`LeftAdjointKernelData.toRightAdjointKernelData`.  It introduces neither a
second comparison record nor a second shift package.  Unlike the conventional
dual twist, the dual cotwist is the unshifted counit cone.

The objectwise comparison remains noncanonical.  Natural comparison data,
equivalence of `H⁰` of the dg counit cone, and shift compatibility are explicit
inputs.  Nothing here constructs those inputs, identifies an inverse kernel,
upgrades the dg functor to a quasi-equivalence, or asserts sphericality.
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
  {E : Correspondence X X W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}

namespace DualCotwistKernelConeData

variable [IsPretriangulated A]
  [Limits.HasZeroObject X] [HasShift X ℤ] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eA.functor.CommShift ℤ]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ]
  (adj : DGAdjunction L S)
  (H : DGAdjunction.H0Presentation (L := L) (R := S) eB eA
    (C'.transform Q) (C.transform P))
  (K : adj.CounitConeData)
  (T : DualCotwistKernelConeData C C' E e P
    (LeftAdjointKernelData.ofH0Presentation H adj) D U)
  (hE : E.KernelEvaluationExact)

section Pointwise

variable [eA.functor.IsTriangulated] [e.equiv.functor.IsTriangulated]

/-- At each source object, the presented dg left-counit triangle is
noncanonically isomorphic to the selected Fourier--Mukai left-counit
triangle. -/
noncomputable abbrev presentedLeftCounitTriangleObjIso (Z : X) :
    (H.presentedCounitTriangle K).obj Z ≅
      (T.dualCotwistTriangleInSource hE).obj Z :=
  CounitKernelConeData.presentedCounitTriangleObjIso adj H K T hE Z

/-- The resulting noncanonical objectwise comparison from the transported dg
counit cone to the selected Fourier--Mukai dual cotwist. -/
noncomputable abbrev transportedDualCotwistObjIso (Z : X) :
    (K.transportedTwist eA).obj Z ≅ T.dualCotwist.obj Z :=
  CounitKernelConeData.transportedTwistObjIso adj H K T hE Z

end Pointwise

/-! ### Supplied natural comparison data -/

/-- Natural comparison data for the presented dg and Fourier--Mukai dual
cotwists.  This is the existing counit/twist comparison after swapping the two
endpoints; no parallel record is introduced. -/
abbrev PresentedDualCotwistComparisonData :=
  CounitKernelConeData.PresentedCounitComparisonData adj H K T hE

namespace PresentedDualCotwistComparisonData

/-- Supply a natural dual-cotwist comparison and the two triangle-map squares
not fixed by the common left-adjunction counit. -/
def ofDualCotwistIso
    (iso : K.transportedTwist eA ≅ T.dualCotwist)
    (second : H.counitToTransportedTwist K ≫ iso.hom =
      T.counitToDualCotwist hE)
    (third : H.transportedTwistToShiftedComposite K =
      iso.hom ≫ T.dualCotwistToShiftedComposite hE) :
    T.PresentedDualCotwistComparisonData adj H K hE :=
  CounitKernelConeData.PresentedCounitComparisonData.ofTwistIso
    adj H K T hE iso second third

section Comparison

variable (N : T.PresentedDualCotwistComparisonData adj H K hE)

/-- The supplied data give a natural comparison of the two left-counit
triangle families. -/
noncomputable abbrev presentedLeftCounitTriangleIso :
    H.presentedCounitTriangle K ≅ T.dualCotwistTriangleInSource hE :=
  CounitKernelConeData.PresentedCounitComparisonData.presentedCounitTriangleIso
    adj H K T hE N

/-- The induced natural isomorphism from the transported dg counit cone to the
selected Fourier--Mukai dual cotwist. -/
noncomputable abbrev transportedDualCotwistIso :
    K.transportedTwist eA ≅ T.dualCotwist :=
  CounitKernelConeData.PresentedCounitComparisonData.transportedTwistIso
    adj H K T hE N

end Comparison

/-- The transported dg counit cone is a kernel functor through the supplied
natural dual-cotwist comparison. -/
theorem transportedDualCotwist_isKernelFunctor
    (N : T.PresentedDualCotwistComparisonData adj H K hE) :
    E.IsKernelFunctor (K.transportedTwist eA) :=
  CounitKernelConeData.PresentedCounitComparisonData.transportedTwist_isKernelFunctor
    adj H K T hE N

/-- An explicit equivalence hypothesis on `H⁰` of the dg counit cone transfers
to the selected Fourier--Mukai dual cotwist. -/
theorem dualCotwist_isEquivalence
    (N : T.PresentedDualCotwistComparisonData adj H K hE)
    (hK : K.twist.h0.IsEquivalence) : T.dualCotwist.IsEquivalence :=
  CounitKernelConeData.PresentedCounitComparisonData.twist_isEquivalence
    adj H K T hE N hK

/-- The selected dual-cotwist kernel, packaged as a kernel autoequivalence
under the explicit `H⁰` equivalence hypothesis. -/
noncomputable abbrev dualCotwistKernelAutoequivalence
    (N : T.PresentedDualCotwistComparisonData adj H K hE)
    (hK : K.twist.h0.IsEquivalence) : KernelAutoequivalence X W :=
  CounitKernelConeData.PresentedCounitComparisonData.twistKernelAutoequivalence
    adj H K T hE N hK

/-! ### Compatibility with selected shift structures -/

variable (N : T.PresentedDualCotwistComparisonData adj H K hE)

/-- Shift compatibility for the dg/Fourier--Mukai dual-cotwist comparison.
This is a semantic alias of the existing twist package, not a second
structure. -/
abbrev ShiftCompatibility :=
  CounitKernelConeData.PresentedCounitComparisonData.ShiftCompatibility
    adj H K T hE N

namespace ShiftCompatibility

open CounitKernelConeData.PresentedCounitComparisonData.ShiftCompatibility

/-- Supply the selected Fourier--Mukai dual-cotwist shift structure and
compatibility of the dg comparison.  The result is the existing twist
compatibility record viewed through the semantic facade. -/
def ofCommShift
    (dualCotwistCommShift : T.dualCotwist.CommShift ℤ)
    (transportedDualCotwistIso_commShift :
      letI : (K.transportedTwist eA).CommShift ℤ :=
        K.twist.transportedH0CommShift
      letI : T.dualCotwist.CommShift ℤ := dualCotwistCommShift
      NatTrans.CommShift N.transportedDualCotwistIso.hom ℤ) :
    N.ShiftCompatibility where
  twistCommShift := dualCotwistCommShift
  transportedTwistIso_commShift := transportedDualCotwistIso_commShift

variable (h : N.ShiftCompatibility)

/-- The selected shift structure on the Fourier--Mukai dual cotwist. -/
abbrev dualCotwistCommShift : T.dualCotwist.CommShift ℤ :=
  h.twistCommShift

/-- The dual-cotwist comparison respects the canonical source shift package
and the selected Fourier--Mukai shift package. -/
theorem transportedDualCotwistIso_commShift :
    letI : (K.transportedTwist eA).CommShift ℤ :=
      K.twist.transportedH0CommShift
    letI : T.dualCotwist.CommShift ℤ := h.dualCotwistCommShift
    NatTrans.CommShift N.transportedDualCotwistIso.hom ℤ :=
  h.transportedTwistIso_commShift

set_option backward.isDefEq.respectTransparency false in
/-- The selected Fourier--Mukai dual cotwist is triangulated when the
comparison respects shifts and the endpoint presentation equivalence is
triangulated. -/
theorem dualCotwistIsTriangulated [eA.functor.IsTriangulated] :
    letI : T.dualCotwist.CommShift ℤ := h.dualCotwistCommShift
    T.dualCotwist.IsTriangulated :=
  twistIsTriangulated adj H K T hE N h

set_option backward.isDefEq.respectTransparency false in
/-- The selected dual-cotwist kernel autoequivalence is exact relative to the
selected target shift package. -/
theorem dualCotwistKernelAutoequivalenceIsTriangulated
    [eA.functor.IsTriangulated] (hK : K.twist.h0.IsEquivalence) :
    letI : (dualCotwistKernelAutoequivalence adj H K T hE N hK).equiv.functor.CommShift ℤ :=
      h.dualCotwistCommShift
    letI : (dualCotwistKernelAutoequivalence adj H K T hE N hK).equiv.inverse.CommShift ℤ :=
      (dualCotwistKernelAutoequivalence adj H K T hE N hK).equiv.commShiftInverse ℤ
    letI : (dualCotwistKernelAutoequivalence adj H K T hE N hK).equiv.CommShift ℤ :=
      (dualCotwistKernelAutoequivalence adj H K T hE N hK).equiv.commShift_of_functor ℤ
    (dualCotwistKernelAutoequivalence adj H K T hE N hK).equiv.IsTriangulated :=
  twistKernelAutoequivalenceIsTriangulated adj H K T hE N h hK

end ShiftCompatibility

end PresentedDualCotwistComparisonData

end DualCotwistKernelConeData

end CategoryTheory.Triangulated.FourierMukai
