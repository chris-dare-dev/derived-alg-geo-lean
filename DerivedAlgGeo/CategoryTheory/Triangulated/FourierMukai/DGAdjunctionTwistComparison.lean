/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionConePresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.FunctorTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.CounitKernel
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionPresentation

/-!
# Comparing presented dg and Fourier--Mukai twists

Suppose a strict dg adjunction is presented on ordinary categories by a pair
of Fourier--Mukai transforms.  A chosen dg cone on its counit and an
independently chosen enhanced Fourier--Mukai cone then give two pointwise
distinguished counit triangles with the same first two vertices and the same
first map.

Mathlib's `isoTriangleOfIso₁₂` supplies a noncanonical isomorphism between
the two triangles at each target object.  Its third component compares the
ordinary transport of the actual dg twist with the Fourier--Mukai twist.

The unconditional completion is chosen separately at each object and
therefore supplies no naturality.  A separate `PresentedCounitComparisonData`
interface records a genuinely supplied natural twist isomorphism and its two
remaining triangle squares; from that input the file constructs the natural
counit-triangle isomorphism.  It does not construct this input or prove
independence of either cone choice.  Under an explicit equivalence hypothesis
on the dg twist at `H⁰`, the comparison packages the selected kernel as a
`KernelAutoequivalence`; it does not prove that hypothesis or sphericality.  A
further `ShiftCompatibility`
refinement can select a Fourier--Mukai `CommShift` structure compatible with
the comparison; exactness then transfers through Mathlib's existing
`Functor.isTriangulated_of_iso` theorem.
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
  {L : DGFunctor A B} {R : DGFunctor B A}
  {eA : H0 A ≌ X} {eB : H0 B ≌ Y}
  {C : Correspondence X Y W₁} {C' : Correspondence Y X W₂}
  {E : Correspondence Y Y W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C' C E} {U : UnitKernelData E}

namespace CounitKernelConeData

variable [IsPretriangulated B]
  [Limits.HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [eB.functor.CommShift ℤ]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ]
  (adj : DGAdjunction L R)
  (H : DGAdjunction.H0Presentation (L := L) (R := R) eA eB
    (C.transform P) (C'.transform Q))
  (K : adj.CounitConeData)
  (S : CounitKernelConeData C C' E e P
    (RightAdjointKernelData.ofH0Presentation H adj) D U)
  (hE : E.KernelEvaluationExact)

section Pointwise

variable [eB.functor.IsTriangulated] [e.equiv.functor.IsTriangulated]

/-- At each target object, the presented dg counit triangle is noncanonically
isomorphic to the independently chosen Fourier--Mukai counit triangle.

The isomorphism is the identity on the adjunction-composite and identity
vertices.  Its third component is the choice made by triangulated-category
completion and is not asserted to be natural in `Z`. -/
noncomputable def presentedCounitTriangleObjIso (Z : Y) :
    (H.presentedCounitTriangle K).obj Z ≅
      (S.counitTriangleInSource hE).obj Z := by
  refine isoTriangleOfIso₁₂ _ _
    (H.presentedCounitTriangle_obj_distinguished K Z)
    (S.counitTriangleInSource_obj_distinguished hE Z)
    (Iso.refl _) (Iso.refl _) ?_
  simp [RightAdjointKernelData.ofH0Presentation_adj]

/-- The first component of the counit-triangle comparison is the identity. -/
@[simp]
theorem presentedCounitTriangleObjIso_hom_hom₁ (Z : Y) :
    ((S.presentedCounitTriangleObjIso adj H K hE Z).hom).hom₁ =
      𝟙 ((C'.transform Q ⋙ C.transform P).obj Z) := by
  simp [presentedCounitTriangleObjIso]

/-- The second component of the counit-triangle comparison is the identity. -/
@[simp]
theorem presentedCounitTriangleObjIso_hom_hom₂ (Z : Y) :
    ((S.presentedCounitTriangleObjIso adj H K hE Z).hom).hom₂ = 𝟙 Z := by
  simp [presentedCounitTriangleObjIso]

/-- The resulting noncanonical objectwise comparison between the transported
actual dg twist and the Fourier--Mukai twist. -/
noncomputable def transportedTwistObjIso (Z : Y) :
    (K.transportedTwist eB).obj Z ≅ S.twist.obj Z :=
  Triangle.π₃.mapIso (S.presentedCounitTriangleObjIso adj H K hE Z)

end Pointwise

/-! ### Supplied natural comparison data -/

/-- The genuinely additional data required to supply a separate natural
counit-cone comparison of the same triangle families considered objectwise
above.

This is a semantic abbreviation of the generic comparison between two
first-map normalizations.  It stores a natural isomorphism of the twist
functors and compatibility with the two remaining triangle maps. -/
abbrev PresentedCounitComparisonData :=
  Triangle.FirstMapNormalizationData.ComparisonData
    (H.counitFirstMapNormalizationData K)
    (S.normalizationData.firstMapNormalizationData hE)

namespace PresentedCounitComparisonData

section Comparison

variable (N : S.PresentedCounitComparisonData adj H K hE)

/-- Supply a natural comparison of the transported dg and Fourier--Mukai
twists, together with exactly the two triangle-map squares not fixed by the
common adjunction counit. -/
def ofTwistIso
    (iso : K.transportedTwist eB ≅ S.twist)
    (second : H.counitToTransportedTwist K ≫ iso.hom =
      S.counitToTwist hE)
    (third : H.transportedTwistToShiftedComposite K =
      iso.hom ≫ S.twistToShiftedComposite hE) :
    S.PresentedCounitComparisonData adj H K hE where
  thirdIso := iso
  second := second
  third := third

/-- The supplied comparison data determine a natural isomorphism between the
presented dg and Fourier--Mukai counit-triangle families. -/
noncomputable def presentedCounitTriangleIso :
    H.presentedCounitTriangle K ≅ S.counitTriangleInSource hE :=
  N.normalizedTriangleIso

/-- The natural counit-triangle comparison is the identity on the adjunction
composite vertex. -/
@[simp]
theorem presentedCounitTriangleIso_hom_app_hom₁ (Z : Y) :
    (N.presentedCounitTriangleIso.hom.app Z).hom₁ =
      𝟙 ((C'.transform Q ⋙ C.transform P).obj Z) :=
  rfl

/-- The natural counit-triangle comparison is the identity on the identity
vertex. -/
@[simp]
theorem presentedCounitTriangleIso_hom_app_hom₂ (Z : Y) :
    (N.presentedCounitTriangleIso.hom.app Z).hom₂ = 𝟙 Z :=
  rfl

/-- The third component of the natural counit-triangle comparison is the
supplied twist isomorphism. -/
@[simp]
theorem presentedCounitTriangleIso_hom_app_hom₃ (Z : Y) :
    (N.presentedCounitTriangleIso.hom.app Z).hom₃ =
      N.thirdIso.hom.app Z :=
  rfl

/-- The induced natural isomorphism from the transported actual dg twist to
the Fourier--Mukai twist. -/
noncomputable def transportedTwistIso :
    K.transportedTwist eB ≅ S.twist :=
  Functor.isoWhiskerRight N.presentedCounitTriangleIso Triangle.π₃

/-- The projected twist isomorphism is the third-vertex isomorphism supplied
by the endpoint-strict comparison data. -/
@[simp]
theorem transportedTwistIso_hom :
    N.transportedTwistIso.hom = N.thirdIso.hom :=
  rfl

end Comparison

/-- The transported actual dg twist is a kernel functor once a natural
comparison with the selected Fourier--Mukai twist has been supplied. -/
theorem transportedTwist_isKernelFunctor
    (N : S.PresentedCounitComparisonData adj H K hE) :
    E.IsKernelFunctor (K.transportedTwist eB) :=
  (S.isKernelFunctor_twist).of_natIso N.transportedTwistIso.symm

/-- An explicit equivalence hypothesis on `H⁰` of the dg twist transfers to the
selected Fourier--Mukai twist through the supplied natural comparison. -/
theorem twist_isEquivalence
    (N : S.PresentedCounitComparisonData adj H K hE)
    (hK : K.twist.h0.IsEquivalence) :
    S.twist.IsEquivalence := by
  letI : (K.transportedTwist eB).IsEquivalence :=
    K.twist.transportedH0_isEquivalence eB eB hK
  exact Functor.isEquivalence_of_iso N.transportedTwistIso

/-- The selected twist kernel, packaged as a kernel autoequivalence under the
explicit equivalence hypothesis on `H⁰` of the dg twist. -/
@[reducible]
noncomputable def twistKernelAutoequivalence
    (N : S.PresentedCounitComparisonData adj H K hE)
    (hK : K.twist.h0.IsEquivalence) : KernelAutoequivalence Y W := by
  letI : (K.transportedTwist eB).IsEquivalence :=
    K.twist.transportedH0_isEquivalence eB eB hK
  letI : S.twist.IsEquivalence :=
    Functor.isEquivalence_of_iso N.transportedTwistIso
  exact
    { corr := E
      kernel := S.twistKernel
      equiv := S.twist.asEquivalence
      iso := S.twistKernelIso.symm }

/-! ### Compatibility with selected shift structures -/

variable (N : S.PresentedCounitComparisonData adj H K hE)

/-- Compatibility of the supplied dg/Fourier--Mukai twist comparison with an
independently selected shift structure on the Fourier--Mukai twist.

The source uses the canonical shift structure on the transported `H⁰` dg
twist.  This record does not manufacture a target structure with
`Functor.CommShift.ofIso`; it records compatibility with the structure chosen
by the realization. -/
structure ShiftCompatibility where
  /-- The selected shift structure on the Fourier--Mukai twist. -/
  twistCommShift : S.twist.CommShift ℤ
  /-- The twist comparison respects the source and target shift structures. -/
  transportedTwistIso_commShift :
    letI : (K.transportedTwist eB).CommShift ℤ :=
      K.twist.transportedH0CommShift
    letI : S.twist.CommShift ℤ := twistCommShift
    NatTrans.CommShift N.transportedTwistIso.hom ℤ

namespace ShiftCompatibility

variable (h : N.ShiftCompatibility)

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier--Mukai twist is triangulated relative to the selected target
shift structure when the supplied comparison respects shifts. -/
theorem twistIsTriangulated [eB.functor.IsTriangulated] :
    letI : S.twist.CommShift ℤ := h.twistCommShift
    S.twist.IsTriangulated := by
  letI : (K.transportedTwist eB).CommShift ℤ :=
    K.twist.transportedH0CommShift
  letI : S.twist.CommShift ℤ := h.twistCommShift
  letI : NatTrans.CommShift N.transportedTwistIso.hom ℤ :=
    h.transportedTwistIso_commShift
  letI : (K.transportedTwist eB).IsTriangulated :=
    K.twist.transportedH0IsTriangulated
  exact Functor.isTriangulated_of_iso N.transportedTwistIso

set_option backward.isDefEq.respectTransparency false in
/-- The kernel autoequivalence of the selected Fourier--Mukai twist is an
exact equivalence relative to the selected target shift package. -/
theorem twistKernelAutoequivalenceIsTriangulated
    [eB.functor.IsTriangulated] (hK : K.twist.h0.IsEquivalence) :
    letI : (twistKernelAutoequivalence adj H K S hE N hK).equiv.functor.CommShift ℤ :=
      h.twistCommShift
    letI : (twistKernelAutoequivalence adj H K S hE N hK).equiv.inverse.CommShift ℤ :=
      (twistKernelAutoequivalence adj H K S hE N hK).equiv.commShiftInverse ℤ
    letI : (twistKernelAutoequivalence adj H K S hE N hK).equiv.CommShift ℤ :=
      (twistKernelAutoequivalence adj H K S hE N hK).equiv.commShift_of_functor ℤ
    (twistKernelAutoequivalence adj H K S hE N hK).equiv.IsTriangulated := by
  letI : (twistKernelAutoequivalence adj H K S hE N hK).equiv.functor.CommShift ℤ :=
    h.twistCommShift
  letI : (twistKernelAutoequivalence adj H K S hE N hK).equiv.inverse.CommShift ℤ :=
    (twistKernelAutoequivalence adj H K S hE N hK).equiv.commShiftInverse ℤ
  letI : (twistKernelAutoequivalence adj H K S hE N hK).equiv.CommShift ℤ :=
    (twistKernelAutoequivalence adj H K S hE N hK).equiv.commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _ h.twistIsTriangulated

end ShiftCompatibility

end PresentedCounitComparisonData

end CounitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
