/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCotwistPresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.AdjunctionUnitKernel
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.DGAdjunctionPresentation

/-!
# Comparing presented dg and Fourier--Mukai cotwists

Suppose a strict dg adjunction is presented on ordinary categories by a pair
of Fourier--Mukai transforms.  A chosen dg cone on its unit and an independently
chosen enhanced Fourier--Mukai cone then give two pointwise distinguished unit
triangles with the same first two vertices and the same first map.

Mathlib's `isoTriangleOfIso₁₂` therefore supplies a noncanonical
isomorphism between the two triangles at each source object.  Applying
`invRotate` gives the corresponding comparison between the conventional
cotwist triangles, with Mathlib retaining ownership of the sign and shift
cancellation.  The first component compares the transported dg cotwist object
with the Fourier--Mukai cotwist object.

The unconditional completion chosen by `isoTriangleOfIso₁₂` is made
separately at each object and therefore supplies no naturality.  A separate
`PresentedUnitComparisonData` interface records a genuinely supplied natural
cone isomorphism and its two remaining triangle squares; from that input the
file constructs natural unit- and cotwist-triangle isomorphisms.  It does not
construct this input or prove independence of either cone choice.  Under an
explicit `H⁰` equivalence hypothesis on the unshifted dg unit cone, the
comparison packages the selected shifted kernel as a `KernelAutoequivalence`;
it does not prove that hypothesis or sphericality.  A further `ShiftCompatibility`
refinement can select a Fourier--Mukai `CommShift`
structure compatible with the conventional cotwist comparison; exactness
then transfers through Mathlib's existing `Functor.isTriangulated_of_iso`
theorem.  Compatibility of the composite comparison from the actual shifted
dg cone is derived from that refinement rather than stored separately.
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
  {E : Correspondence X X W} {P : W₁} {Q : W₂}
  {e : Enhancement.{vE, uE} W}
  {D : ConvolutionData C C' E} {U : UnitKernelData E}

namespace AdjunctionUnitKernelConeData

variable [IsPretriangulated A]
  [Limits.HasZeroObject X] [HasShift X ℤ] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eA.functor.CommShift ℤ]
  [Limits.HasZeroObject W] [HasShift W ℤ] [Preadditive W]
  [∀ n : ℤ, (shiftFunctor W n).Additive] [Pretriangulated W]
  [e.equiv.functor.CommShift ℤ]
  (adj : DGAdjunction L R)
  (H : DGAdjunction.H0Presentation (L := L) (R := R) eA eB
    (C.transform P) (C'.transform Q))
  (K : adj.UnitConeData)
  (S : AdjunctionUnitKernelConeData C C' E e P
    (RightAdjointKernelData.ofH0Presentation H adj) D U)
  (hE : E.KernelEvaluationExact)

section Pointwise

variable [eA.functor.IsTriangulated] [e.equiv.functor.IsTriangulated]

/-- At each object, the presented dg unit triangle is noncanonically
isomorphic to the independently chosen Fourier--Mukai unit triangle.

The isomorphism is the identity on the identity and adjunction-composite
vertices.  Its third component is the choice made by triangulated-category
completion and is not asserted to be natural in `Z`. -/
noncomputable def presentedUnitTriangleObjIso (Z : X) :
    (H.presentedUnitTriangle K).obj Z ≅
      (S.unitTriangleInSource hE).obj Z := by
  refine isoTriangleOfIso₁₂ _ _
    (H.presentedUnitTriangle_obj_distinguished K Z)
    (S.unitTriangleInSource_obj_distinguished hE Z)
    (Iso.refl _) (Iso.refl _) ?_
  simp [RightAdjointKernelData.ofH0Presentation_adj]

/-- The first component of the unit-triangle comparison is the identity. -/
@[simp]
theorem presentedUnitTriangleObjIso_hom_hom₁ (Z : X) :
    ((S.presentedUnitTriangleObjIso adj H K hE Z).hom).hom₁ = 𝟙 Z := by
  simp [presentedUnitTriangleObjIso]

/-- The second component of the unit-triangle comparison is the identity. -/
@[simp]
theorem presentedUnitTriangleObjIso_hom_hom₂ (Z : X) :
    ((S.presentedUnitTriangleObjIso adj H K hE Z).hom).hom₂ =
      𝟙 ((C.transform P ⋙ C'.transform Q).obj Z) := by
  simp [presentedUnitTriangleObjIso]

/-- The resulting noncanonical objectwise comparison between the transported
dg unit cone and the Fourier--Mukai unit cone. -/
noncomputable def transportedUnitConeObjIso (Z : X) :
    (K.transportedUnitCone eA).obj Z ≅ S.cotwistCone.obj Z :=
  Triangle.π₃.mapIso (S.presentedUnitTriangleObjIso adj H K hE Z)

/-- Inverse rotation of the unit-triangle comparison gives a noncanonical
objectwise comparison of the conventional cotwist triangles. -/
noncomputable def presentedCotwistTriangleObjIso (Z : X) :
    (H.presentedCotwistTriangle K).obj Z ≅
      (S.cotwistTriangleInSource hE).obj Z :=
  (invRotate X).mapIso (S.presentedUnitTriangleObjIso adj H K hE Z)

/-- The second component of the cotwist-triangle comparison is the identity. -/
@[simp]
theorem presentedCotwistTriangleObjIso_hom_hom₂ (Z : X) :
    ((S.presentedCotwistTriangleObjIso adj H K hE Z).hom).hom₂ = 𝟙 Z := by
  simp [presentedCotwistTriangleObjIso]

/-- The third component of the cotwist-triangle comparison is the identity. -/
@[simp]
theorem presentedCotwistTriangleObjIso_hom_hom₃ (Z : X) :
    ((S.presentedCotwistTriangleObjIso adj H K hE Z).hom).hom₃ =
      𝟙 ((C.transform P ⋙ C'.transform Q).obj Z) := by
  simp [presentedCotwistTriangleObjIso]

/-- The resulting noncanonical objectwise comparison between the transported
dg cotwist and the Fourier--Mukai cotwist. -/
noncomputable def transportedCotwistObjIso (Z : X) :
    (K.transportedCotwist eA).obj Z ≅ S.cotwist.obj Z :=
  Triangle.π₁.mapIso (S.presentedCotwistTriangleObjIso adj H K hE Z)

/-- The actual shifted dg cone, after `H⁰` and ordinary transport, is
noncanonically objectwise isomorphic to the Fourier--Mukai cotwist. -/
noncomputable def transportedDGCotwistObjIso (Z : X) :
    (K.transportedDGCotwist eA).obj Z ≅ S.cotwist.obj Z :=
  (K.transportedCotwistH0Iso (eC := eA)).app Z ≪≫
    S.transportedCotwistObjIso adj H K hE Z

end Pointwise

/-! ### Supplied natural comparison data -/

/-- The genuinely additional data required to supply a separate natural
unit-cone comparison of the same triangle families considered objectwise
above.

This is a semantic abbreviation of the generic comparison between two
first-map normalizations.  It stores a natural isomorphism of the unit-cone
functors and compatibility with the two remaining triangle maps. -/
abbrev PresentedUnitComparisonData :=
  Triangle.FirstMapNormalizationData.ComparisonData
    (H.unitFirstMapNormalizationData K)
    (S.normalizationData.firstMapNormalizationData hE)

namespace PresentedUnitComparisonData

section Comparison

variable (N : S.PresentedUnitComparisonData adj H K hE)

/-- Supply a natural comparison of the transported dg and Fourier--Mukai unit
cones, together with exactly the two triangle-map squares not fixed by the
common adjunction unit. -/
def ofConeIso
    (iso : K.transportedUnitCone eA ≅ S.cotwistCone)
    (second : H.compositeToTransportedUnitCone K ≫ iso.hom =
      S.compositeToCotwistCone hE)
    (third : H.transportedUnitConeToShiftedIdentity K =
      iso.hom ≫ S.cotwistConeToShiftedIdentity hE) :
    S.PresentedUnitComparisonData adj H K hE where
  thirdIso := iso
  second := second
  third := third

/-- The supplied comparison data determine a natural isomorphism between the
presented dg and Fourier--Mukai unit-triangle families. -/
noncomputable def presentedUnitTriangleIso :
    H.presentedUnitTriangle K ≅ S.unitTriangleInSource hE :=
  N.normalizedTriangleIso

/-- The natural unit-triangle comparison is the identity on the identity
vertex. -/
@[simp]
theorem presentedUnitTriangleIso_hom_app_hom₁ (Z : X) :
    (N.presentedUnitTriangleIso.hom.app Z).hom₁ = 𝟙 Z :=
  rfl

/-- The natural unit-triangle comparison is the identity on the adjunction
composite vertex. -/
@[simp]
theorem presentedUnitTriangleIso_hom_app_hom₂ (Z : X) :
    (N.presentedUnitTriangleIso.hom.app Z).hom₂ =
      𝟙 ((C.transform P ⋙ C'.transform Q).obj Z) :=
  rfl

/-- The third component of the natural unit-triangle comparison is the
supplied unit-cone isomorphism. -/
@[simp]
theorem presentedUnitTriangleIso_hom_app_hom₃ (Z : X) :
    (N.presentedUnitTriangleIso.hom.app Z).hom₃ =
      N.thirdIso.hom.app Z :=
  rfl

/-- The supplied natural isomorphism between the two unshifted unit-cone
functors. -/
noncomputable def transportedUnitConeIso :
    K.transportedUnitCone eA ≅ S.cotwistCone :=
  N.thirdIso

/-- Inverse rotation upgrades the natural unit-triangle comparison to a
natural comparison of the conventional cotwist triangles. -/
noncomputable def presentedCotwistTriangleIso :
    H.presentedCotwistTriangle K ≅ S.cotwistTriangleInSource hE :=
  Functor.isoWhiskerRight N.presentedUnitTriangleIso (invRotate X)

/-- The natural cotwist-triangle comparison is the identity on its identity
vertex. -/
@[simp]
theorem presentedCotwistTriangleIso_hom_app_hom₂ (Z : X) :
    (N.presentedCotwistTriangleIso.hom.app Z).hom₂ = 𝟙 Z :=
  rfl

/-- The natural cotwist-triangle comparison is the identity on its adjunction
composite vertex. -/
@[simp]
theorem presentedCotwistTriangleIso_hom_app_hom₃ (Z : X) :
    (N.presentedCotwistTriangleIso.hom.app Z).hom₃ =
      𝟙 ((C.transform P ⋙ C'.transform Q).obj Z) :=
  rfl

/-- The induced natural isomorphism from the conventional transported dg
cotwist to the Fourier--Mukai cotwist. -/
noncomputable def transportedCotwistIso :
    K.transportedCotwist eA ≅ S.cotwist :=
  Functor.isoWhiskerRight N.presentedCotwistTriangleIso Triangle.π₁

/-- The transport of the actual shifted dg unit cone is naturally isomorphic
to the Fourier--Mukai cotwist. -/
noncomputable def transportedDGCotwistIso :
    K.transportedDGCotwist eA ≅ S.cotwist :=
  K.transportedCotwistH0Iso (eC := eA) ≪≫ N.transportedCotwistIso

end Comparison

/-- The conventional transported dg cotwist is a kernel functor once a
natural comparison with the selected Fourier--Mukai cotwist has been
supplied. -/
theorem transportedCotwist_isKernelFunctor
    (N : S.PresentedUnitComparisonData adj H K hE) :
    E.IsKernelFunctor (K.transportedCotwist eA) :=
  (S.isKernelFunctor_cotwist hE.toCommShift).of_natIso
    N.transportedCotwistIso.symm

/-- The transport of the actual shifted dg unit cone is a kernel functor
through the composite natural comparison. -/
theorem transportedDGCotwist_isKernelFunctor
    (N : S.PresentedUnitComparisonData adj H K hE) :
    E.IsKernelFunctor (K.transportedDGCotwist eA) :=
  (S.isKernelFunctor_cotwist hE.toCommShift).of_natIso
    N.transportedDGCotwistIso.symm

/-- An explicit equivalence hypothesis on `H⁰` of the unshifted dg unit cone
transfers to the selected conventional Fourier--Mukai cotwist. -/
theorem cotwist_isEquivalence
    (N : S.PresentedUnitComparisonData adj H K hE)
    (hK : K.unitCone.h0.IsEquivalence) :
    S.cotwist.IsEquivalence := by
  letI : (K.transportedCotwist eA).IsEquivalence :=
    K.transportedCotwist_isEquivalence hK
  exact Functor.isEquivalence_of_iso N.transportedCotwistIso

/-- The selected shifted cotwist kernel, packaged as a kernel autoequivalence
under the explicit equivalence hypothesis on `H⁰` of the unshifted dg unit
cone. -/
@[reducible]
noncomputable def cotwistKernelAutoequivalence
    (N : S.PresentedUnitComparisonData adj H K hE)
    (hK : K.unitCone.h0.IsEquivalence) : KernelAutoequivalence X W := by
  letI : (K.transportedCotwist eA).IsEquivalence :=
    K.transportedCotwist_isEquivalence hK
  letI : S.cotwist.IsEquivalence :=
    Functor.isEquivalence_of_iso N.transportedCotwistIso
  exact
    { corr := E
      kernel := S.cotwistKernel
      equiv := S.cotwist.asEquivalence
      iso := (S.cotwistKernelIso hE.toCommShift).symm }

/-! ### Compatibility with selected shift structures -/

variable (N : S.PresentedUnitComparisonData adj H K hE)

/-- Compatibility of the supplied conventional dg/Fourier--Mukai cotwist
comparison with an independently selected shift structure on the
Fourier--Mukai cotwist.

The source uses the canonical sign-correct shift structure on the conventional
pointwise `[-1]` cotwist.  Compatibility of the intermediate comparison from
the actual shifted dg cone is derived canonically and is not stored here. -/
structure ShiftCompatibility where
  /-- The selected shift structure on the Fourier--Mukai cotwist. -/
  cotwistCommShift : S.cotwist.CommShift ℤ
  /-- The conventional cotwist comparison respects the source and target
  shift structures. -/
  transportedCotwistIso_commShift :
    letI : (K.transportedCotwist eA).CommShift ℤ :=
      K.transportedCotwistCommShift (eC := eA)
    letI : S.cotwist.CommShift ℤ := cotwistCommShift
    NatTrans.CommShift N.transportedCotwistIso.hom ℤ

namespace ShiftCompatibility

variable (h : N.ShiftCompatibility)

set_option backward.isDefEq.respectTransparency false in
/-- The composite comparison from the actual shifted dg cotwist to the
Fourier--Mukai cotwist respects the canonical source shift package and the
selected Fourier--Mukai shift package. -/
theorem transportedDGCotwistIso_commShift [eA.functor.Additive] :
    letI : (K.transportedDGCotwist eA).CommShift ℤ :=
      (K.unitCone.shiftedFunctor (-1 : ℤ)).transportedH0CommShift
    letI : S.cotwist.CommShift ℤ := h.cotwistCommShift
    NatTrans.CommShift N.transportedDGCotwistIso.hom ℤ := by
  letI : (K.transportedDGCotwist eA).CommShift ℤ :=
    (K.unitCone.shiftedFunctor (-1 : ℤ)).transportedH0CommShift
  letI : (K.transportedCotwist eA).CommShift ℤ :=
    K.transportedCotwistCommShift (eC := eA)
  letI : S.cotwist.CommShift ℤ := h.cotwistCommShift
  letI : NatTrans.CommShift (K.transportedCotwistH0Iso (eC := eA)).hom ℤ :=
    K.transportedCotwistH0Iso_commShift (eC := eA)
  letI : NatTrans.CommShift N.transportedCotwistIso.hom ℤ :=
    h.transportedCotwistIso_commShift
  change NatTrans.CommShift
    ((K.transportedCotwistH0Iso (eC := eA)).hom ≫
      N.transportedCotwistIso.hom) ℤ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier--Mukai cotwist is triangulated relative to the selected target
shift structure when the conventional cotwist comparison respects shifts. -/
theorem cotwistIsTriangulated [eA.functor.IsTriangulated] :
    letI : S.cotwist.CommShift ℤ := h.cotwistCommShift
    S.cotwist.IsTriangulated := by
  letI : (K.transportedCotwist eA).CommShift ℤ :=
    K.transportedCotwistCommShift (eC := eA)
  letI : S.cotwist.CommShift ℤ := h.cotwistCommShift
  letI : NatTrans.CommShift N.transportedCotwistIso.hom ℤ :=
    h.transportedCotwistIso_commShift
  letI : (K.transportedCotwist eA).IsTriangulated :=
    K.transportedCotwistIsTriangulated (eC := eA)
  exact Functor.isTriangulated_of_iso N.transportedCotwistIso

set_option backward.isDefEq.respectTransparency false in
/-- The kernel autoequivalence of the selected Fourier--Mukai cotwist is an
exact equivalence relative to the selected target shift package. -/
theorem cotwistKernelAutoequivalenceIsTriangulated
    [eA.functor.IsTriangulated] (hK : K.unitCone.h0.IsEquivalence) :
    letI : (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.functor.CommShift ℤ :=
      h.cotwistCommShift
    letI : (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.inverse.CommShift ℤ :=
      (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.commShiftInverse ℤ
    letI : (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.CommShift ℤ :=
      (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.commShift_of_functor ℤ
    (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.IsTriangulated := by
  letI : (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.functor.CommShift ℤ :=
    h.cotwistCommShift
  letI : (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.inverse.CommShift ℤ :=
    (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.commShiftInverse ℤ
  letI : (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.CommShift ℤ :=
    (cotwistKernelAutoequivalence adj H K S hE N hK).equiv.commShift_of_functor ℤ
  exact Equivalence.IsTriangulated.mk' _ h.cotwistIsTriangulated

end ShiftCompatibility

end PresentedUnitComparisonData

end AdjunctionUnitKernelConeData

end CategoryTheory.Triangulated.FourierMukai
