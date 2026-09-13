/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.AdjunctionH0Presentation
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCone
import DerivedAlgGeo.CategoryTheory.Triangulated.TriangleFunctorNormalization

/-!
# Presenting dg-adjunction cone triangles on ordinary categories

A strict dg adjunction and a choice of cones for its counit give a natural
family of distinguished triangles on the target homotopy category.  A
`DGAdjunction.H0Presentation` identifies the transported left and right
functors with named ordinary functors `F` and `G` on categories `X` and `Y`.

This file transports the raw dg counit triangle through the target equivalence
and feeds its endpoint comparisons to
`Triangle.FirstMapNormalizationData`.  The resulting family has literal first
map `(P.toAdjunction A).counit : G ⋙ F ⟶ 𝟭 Y`, literal first two vertices, and
the transported dg twist as its unchanged third vertex.

For the counit side, the target equivalence's `CommShift` and triangulatedness
are supplied where needed; for the unit side, the corresponding data are
supplied on the source equivalence.  A plain category equivalence provides
neither.  The construction does not identify the
transported dg twist with an independently chosen ordinary or
Fourier--Mukai twist, make it exact, or assert sphericality.

The unit-side mirror transports the raw dg unit-cone triangle through the
source equivalence and normalizes it to have literal first map
`(P.toAdjunction A).unit : 𝟭 X ⟶ F ⋙ G`.  Its third vertex is the
transported *unshifted* unit cone.  No inverse rotation or identification with
the conventional `[-1]` cotwist is performed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v vX vY uC uD uX uY

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace DGAdjunction

variable {C : Type uC} {D : Type uD} {X : Type uX} {Y : Type uY}
  [DGCategory.{v} C] [DGCategory.{v} D]
  [Category.{vX} X] [Category.{vY} Y]
  {L : DGFunctor C D} {R : DGFunctor D C}
  {eC : H0 C ≌ X} {eD : H0 D ≌ Y}
  {F : X ⥤ Y} {G : Y ⥤ X}
  {A : DGAdjunction L R}

private theorem whiskeredH0IdIso_hom_app (Z : Y) :
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eD.inverse (DGFunctor.h0IdIso (C := D)))
      eD.functor).hom.app Z = 𝟙 _ := by
  change eD.functor.map (𝟙 (eD.inverse.obj Z)) = 𝟙 _
  exact eD.functor.map_id _

private theorem whiskeredRightUnitor_hom_app (Z : Y) :
    (Functor.isoWhiskerRight (Functor.rightUnitor eD.inverse)
      eD.functor).hom.app Z = 𝟙 _ := by
  change eD.functor.map (𝟙 (eD.inverse.obj Z)) = 𝟙 _
  exact eD.functor.map_id _

private theorem whiskeredH0CompIso_hom_app (Z : Y) :
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft eD.inverse (DGFunctor.h0CompIso R L))
      eD.functor).hom.app Z = 𝟙 _ := by
  change eD.functor.map (𝟙 ((R.h0 ⋙ L.h0).obj (eD.inverse.obj Z))) = 𝟙 _
  exact eD.functor.map_id _

private theorem whiskeredAssociator_hom_app (Z : Y) :
    (Functor.isoWhiskerRight
      (Functor.associator eD.inverse R.h0 eC.functor)
      (eC.inverse ⋙ (L.h0 ⋙ eD.functor))).hom.app Z = 𝟙 _ := by
  change eD.functor.map (L.h0.map (eC.inverse.map (𝟙 _))) = 𝟙 _
  rw [eC.inverse.map_id, L.h0.map_id, eD.functor.map_id]

namespace CounitConeData

variable [IsPretriangulated D] (K : A.CounitConeData)

/-- The dg counit cone functor transported from `H⁰ D` to the ordinary target
category.  No exactness is asserted. -/
noncomputable abbrev transportedTwist (eD : H0 D ≌ Y) : Y ⥤ Y :=
  eD.inverse ⋙ K.twist.h0 ⋙ eD.functor

variable [HasShift Y ℤ] [eD.functor.CommShift ℤ]

/-- The raw dg counit triangle, reindexed along the target equivalence and
mapped to the ordinary target category. -/
noncomputable def rawTransportedTwistTriangle : Y ⥤ Triangle Y :=
  (eD.inverse ⋙ K.twistTriangleFunctor A) ⋙ eD.functor.mapTriangle

@[simp]
theorem rawTransportedTwistTriangle_obj_obj₃ (Z : Y) :
    ((K.rawTransportedTwistTriangle (eD := eD)).obj Z).obj₃ =
      (K.transportedTwist eD).obj Z :=
  rfl

@[simp]
theorem rawTransportedTwistTriangle_obj_mor₁ (Z : Y) :
    ((K.rawTransportedTwistTriangle (eD := eD)).obj Z).mor₁ =
      eD.functor.map (A.h0Counit.app (eD.inverse.obj Z)) := by
  change eD.functor.map
    (((K.twistTriangleFunctor A).obj (eD.inverse.obj Z)).mor₁) = _
  rw [K.twistTriangleFunctor_obj_mor₁ A]
  rfl

/-- The second projection of the raw transported dg counit triangle,
identified with the identity functor of the ordinary target category. -/
noncomputable def rawTransportedTwistTriangleObj₂Iso :
    K.rawTransportedTwistTriangle (eD := eD) ⋙ Triangle.π₂ ≅ 𝟭 Y := by
  exact
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eD.inverse (DGFunctor.h0IdIso (C := D)))
        eD.functor ≪≫
      Functor.isoWhiskerRight (Functor.rightUnitor eD.inverse) eD.functor ≪≫
      eD.counitIso

@[simp]
theorem rawTransportedTwistTriangleObj₂Iso_hom_app (Z : Y) :
    (K.rawTransportedTwistTriangleObj₂Iso (eD := eD)).hom.app Z =
      eD.counit.app Z := by
  simp only [rawTransportedTwistTriangleObj₂Iso, Iso.trans_hom,
    NatTrans.comp_app]
  rw [whiskeredH0IdIso_hom_app (eD := eD),
    whiskeredRightUnitor_hom_app (eD := eD)]
  change 𝟙 (eD.functor.obj (eD.inverse.obj Z)) ≫ 𝟙 _ ≫
    eD.counit.app Z = eD.counit.app Z
  simp

private noncomputable def transportedH0CounitApp (Z : Y) :
    (K.rawTransportedTwistTriangle (eD := eD) ⋙ Triangle.π₁).obj Z ⟶
      (𝟭 Y).obj Z :=
  eD.functor.map (A.h0Counit.app (eD.inverse.obj Z)) ≫ eD.counit.app Z

private theorem rawTransportedTwistTriangle_mor₁_comp_obj₂Iso_hom_app (Z : Y) :
    (Functor.whiskerLeft (K.rawTransportedTwistTriangle (eD := eD))
          Triangle.π₁Toπ₂).app Z ≫
        (K.rawTransportedTwistTriangleObj₂Iso (eD := eD)).hom.app Z =
      transportedH0CounitApp (L := L) (R := R) (A := A) (eD := eD) K Z := by
  change ((K.rawTransportedTwistTriangle (eD := eD)).obj Z).mor₁ ≫
      (K.rawTransportedTwistTriangleObj₂Iso (eD := eD)).hom.app Z = _
  rw [K.rawTransportedTwistTriangle_obj_mor₁,
    K.rawTransportedTwistTriangleObj₂Iso_hom_app]
  rfl

section Distinguished

variable [Limits.HasZeroObject Y] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [eD.functor.IsTriangulated]

/-- Every value of the transported raw dg counit triangle is distinguished
when the target equivalence is triangulated. -/
theorem rawTransportedTwistTriangle_obj_distinguished (Z : Y) :
    (K.rawTransportedTwistTriangle (eD := eD)).obj Z ∈ distTriang Y := by
  exact eD.functor.map_distinguished _
    (K.twistTriangleFunctor_obj_mem_distinguishedTriangles A (eD.inverse.obj Z))

end Distinguished

end CounitConeData

namespace UnitConeData

variable [IsPretriangulated C] (K : A.UnitConeData)

/-- The dg unit-cone functor transported from `H⁰ C` to the ordinary source
category.  This is the unshifted cone; no cotwist shift or exactness is
asserted. -/
noncomputable abbrev transportedUnitCone (eC : H0 C ≌ X) : X ⥤ X :=
  eC.inverse ⋙ K.unitCone.h0 ⋙ eC.functor

variable [HasShift X ℤ] [eC.functor.CommShift ℤ]

/-- The raw dg unit triangle, reindexed along the source equivalence and
mapped to the ordinary source category. -/
noncomputable def rawTransportedUnitTriangle : X ⥤ Triangle X :=
  (eC.inverse ⋙ K.unitTriangleFunctor A) ⋙ eC.functor.mapTriangle

@[simp]
theorem rawTransportedUnitTriangle_obj_obj₃ (Z : X) :
    ((K.rawTransportedUnitTriangle (eC := eC)).obj Z).obj₃ =
      (K.transportedUnitCone eC).obj Z :=
  rfl

@[simp]
theorem rawTransportedUnitTriangle_obj_mor₁ (Z : X) :
    ((K.rawTransportedUnitTriangle (eC := eC)).obj Z).mor₁ =
      eC.functor.map (A.h0Unit.app (eC.inverse.obj Z)) := by
  change eC.functor.map
    (((K.unitTriangleFunctor A).obj (eC.inverse.obj Z)).mor₁) = _
  rw [K.unitTriangleFunctor_obj_mor₁ A]
  rfl

/-- The first projection of the raw transported dg unit triangle, identified
with the identity functor of the ordinary source category. -/
noncomputable def rawTransportedUnitTriangleObj₁Iso :
    K.rawTransportedUnitTriangle (eC := eC) ⋙ Triangle.π₁ ≅ 𝟭 X := by
  exact
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eC.inverse (DGFunctor.h0IdIso (C := C)))
        eC.functor ≪≫
      Functor.isoWhiskerRight (Functor.rightUnitor eC.inverse) eC.functor ≪≫
      eC.counitIso

@[simp]
theorem rawTransportedUnitTriangleObj₁Iso_hom_app (Z : X) :
    (K.rawTransportedUnitTriangleObj₁Iso (eC := eC)).hom.app Z =
      eC.counit.app Z := by
  simp only [rawTransportedUnitTriangleObj₁Iso, Iso.trans_hom,
    NatTrans.comp_app]
  rw [whiskeredH0IdIso_hom_app (eD := eC),
    whiskeredRightUnitor_hom_app (eD := eC)]
  change 𝟙 (eC.functor.obj (eC.inverse.obj Z)) ≫ 𝟙 _ ≫
    eC.counit.app Z = eC.counit.app Z
  simp

section Distinguished

variable [Limits.HasZeroObject X] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eC.functor.IsTriangulated]

/-- Every value of the transported raw dg unit triangle is distinguished
when the source equivalence is triangulated. -/
theorem rawTransportedUnitTriangle_obj_distinguished (Z : X) :
    (K.rawTransportedUnitTriangle (eC := eC)).obj Z ∈ distTriang X := by
  exact eC.functor.map_distinguished _
    (K.unitTriangleFunctor_obj_mem_distinguishedTriangles A (eC.inverse.obj Z))

end Distinguished

end UnitConeData

namespace H0Presentation

variable [IsPretriangulated D] [HasShift Y ℤ]
  [eD.functor.CommShift ℤ]
  (P : H0Presentation (L := L) (R := R) eC eD F G)
  (K : A.CounitConeData)

/-- The first projection of the raw transported dg counit triangle, identified
with the composite of the named presented right and left adjoints. -/
noncomputable def counitTriangleObj₁Iso :
    K.rawTransportedTwistTriangle (eD := eD) ⋙ Triangle.π₁ ≅ G ⋙ F := by
  let right₀ := transportedH0Right (R := R) eC eD
  exact
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eD.inverse (DGFunctor.h0CompIso R L))
        eD.functor ≪≫
      Functor.associator eD.inverse (R.h0 ⋙ L.h0) eD.functor ≪≫
      Functor.isoWhiskerLeft eD.inverse
        (Functor.associator R.h0 L.h0 eD.functor) ≪≫
      (Functor.associator eD.inverse R.h0 (L.h0 ⋙ eD.functor)).symm ≪≫
      Functor.isoWhiskerLeft (eD.inverse ⋙ R.h0)
        (eC.funInvIdAssoc (L.h0 ⋙ eD.functor)).symm ≪≫
      (Functor.associator (eD.inverse ⋙ R.h0) eC.functor
        (eC.inverse ⋙ (L.h0 ⋙ eD.functor))).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator eD.inverse R.h0 eC.functor)
        (eC.inverse ⋙ (L.h0 ⋙ eD.functor)) ≪≫
      Functor.isoWhiskerLeft right₀
        (Functor.associator eC.inverse L.h0 eD.functor).symm ≪≫
      Functor.isoWhiskerLeft right₀ P.leftIso ≪≫
      Functor.isoWhiskerRight P.rightIso F

private noncomputable def counitSourceUnitApp (Z : Y) :
    (K.rawTransportedTwistTriangle (eD := eD) ⋙ Triangle.π₁).obj Z ⟶
      (transportedH0Left (L := L) eC eD).obj
        ((transportedH0Right (R := R) eC eD).obj Z) :=
  eD.functor.map
    (L.h0.map (eC.unit.app (R.h0.obj (eD.inverse.obj Z))))

private noncomputable def rightIsoHomMapApp (Z : Y) :
    F.obj ((transportedH0Right (R := R) eC eD).obj Z) ⟶
      (G ⋙ F).obj Z :=
  F.map (P.rightIso.hom.app Z)

private noncomputable def rightIsoInvMapApp (Z : Y) :
    (G ⋙ F).obj Z ⟶
      F.obj ((transportedH0Right (R := R) eC eD).obj Z) :=
  F.map (P.rightIso.inv.app Z)

omit [IsPretriangulated D] [HasShift Y ℤ] [eD.functor.CommShift ℤ] in
@[reassoc]
private theorem rightIsoHomMapApp_comp_rightIsoInvMapApp (Z : Y) :
    rightIsoHomMapApp (R := R) (eC := eC) (eD := eD) P Z ≫
        rightIsoInvMapApp (R := R) (eC := eC) (eD := eD) P Z =
      𝟙 _ := by
  change
    (Functor.isoWhiskerRight P.rightIso F).hom.app Z ≫
        (Functor.isoWhiskerRight P.rightIso F).inv.app Z = 𝟙 _
  exact (Functor.isoWhiskerRight P.rightIso F).hom_inv_id_app Z

private noncomputable def presentedObj₁IsoHomApp (Z : Y) :
    (K.rawTransportedTwistTriangle (eD := eD) ⋙ Triangle.π₁).obj Z ⟶
      (G ⋙ F).obj Z :=
  counitSourceUnitApp (L := L) (R := R) (eC := eC) (eD := eD) K Z ≫
    P.leftIso.hom.app
      ((transportedH0Right (R := R) eC eD).obj Z) ≫
    rightIsoHomMapApp (R := R) (eC := eC) (eD := eD) P Z

private theorem counitTriangleObj₁Iso_hom_app (Z : Y) :
    (P.counitTriangleObj₁Iso K).hom.app Z =
      counitSourceUnitApp (L := L) (R := R) (eC := eC) (eD := eD) K Z ≫
        P.leftIso.hom.app
          ((transportedH0Right (R := R) eC eD).obj Z) ≫
        F.map (P.rightIso.hom.app Z) := by
  simp only [counitTriangleObj₁Iso, Iso.trans_hom, NatTrans.comp_app]
  rw [whiskeredH0CompIso_hom_app (eD := eD),
    whiskeredAssociator_hom_app (eC := eC) (eD := eD)]
  simp
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  rfl

private theorem counitTriangleObj₁Iso_hom_app_eq_presentedObj₁IsoHomApp
    (Z : Y) :
    (P.counitTriangleObj₁Iso K).hom.app Z =
      presentedObj₁IsoHomApp (L := L) (R := R) (eC := eC) (eD := eD)
        P K Z := by
  rw [P.counitTriangleObj₁Iso_hom_app]
  rfl

private noncomputable def presentedCounitApp (Z : Y) :
    (G ⋙ F).obj Z ⟶ (𝟭 Y).obj Z :=
  rightIsoInvMapApp (R := R) (eC := eC) (eD := eD) P Z ≫
    P.leftIso.inv.app ((transportedH0Right (R := R) eC eD).obj Z) ≫
    (A.transportedH0 eC eD).counit.app Z

omit [IsPretriangulated D] [HasShift Y ℤ] [eD.functor.CommShift ℤ] in
private theorem toAdjunction_counit_app_eq_presentedCounitApp (Z : Y) :
    (P.toAdjunction A).counit.app Z =
      presentedCounitApp (A := A) (eC := eC) (eD := eD) P Z := by
  rw [P.toAdjunction_counit_app A]
  rfl

private theorem counitSourceUnitApp_comp_transportedH0_counit (Z : Y) :
    counitSourceUnitApp (L := L) (R := R) (eC := eC) (eD := eD) K Z ≫
        (A.transportedH0 eC eD).counit.app Z =
      CounitConeData.transportedH0CounitApp
        (L := L) (R := R) (A := A) (eD := eD) K Z := by
  unfold counitSourceUnitApp CounitConeData.transportedH0CounitApp
  rw [A.transportedH0_counit_app eC eD]
  simp only [Equivalence.symm_counit, Equivalence.toAdjunction_counit,
    Functor.map_comp, Category.assoc]
  let i := eD.functor.mapIso
    (L.h0.mapIso (eC.unitIso.app (R.h0.obj (eD.inverse.obj Z))))
  change i.hom ≫ i.inv ≫
      eD.functor.map (A.h0Counit.app (eD.inverse.obj Z)) ≫
        eD.counit.app Z =
    eD.functor.map (A.h0Counit.app (eD.inverse.obj Z)) ≫ eD.counit.app Z
  rw [Iso.hom_inv_id_assoc]
  rfl

private theorem presentedObj₁IsoHomApp_comp_counit (Z : Y) :
    presentedObj₁IsoHomApp (L := L) (R := R) (eC := eC) (eD := eD)
          P K Z ≫
        (P.toAdjunction A).counit.app Z =
      CounitConeData.transportedH0CounitApp
        (L := L) (R := R) (A := A) (eD := eD) K Z := by
  rw [P.toAdjunction_counit_app_eq_presentedCounitApp]
  unfold presentedObj₁IsoHomApp presentedCounitApp
  simp only [Category.assoc]
  rw [rightIsoHomMapApp_comp_rightIsoInvMapApp_assoc]
  rw [Iso.hom_inv_id_app_assoc]
  exact counitSourceUnitApp_comp_transportedH0_counit (K := K) Z

/-- The generic first-map normalization data for the transported dg counit
triangle.  Its named first map is exactly the counit of the ordinary
adjunction constructed by `P`. -/
noncomputable def counitFirstMapNormalizationData :
    Triangle.FirstMapNormalizationData
      (K.rawTransportedTwistTriangle (eD := eD)) (G ⋙ F) (𝟭 Y)
        (P.toAdjunction A).counit where
  obj₁Iso := P.counitTriangleObj₁Iso K
  obj₂Iso := K.rawTransportedTwistTriangleObj₂Iso (eD := eD)
  square := by
    ext Z
    simp only [NatTrans.comp_app]
    rw [K.rawTransportedTwistTriangle_mor₁_comp_obj₂Iso_hom_app,
      P.counitTriangleObj₁Iso_hom_app_eq_presentedObj₁IsoHomApp,
      P.presentedObj₁IsoHomApp_comp_counit K]

/-- The second map of the presented counit triangle, from the identity to the
transported dg twist. -/
noncomputable def counitToTransportedTwist :
    𝟭 Y ⟶ K.transportedTwist eD :=
  (P.counitFirstMapNormalizationData K).normalizedSecond

/-- The connecting map of the presented counit triangle, from the transported
dg twist to the shift of the presented adjunction composite. -/
noncomputable def transportedTwistToShiftedComposite :
    K.transportedTwist eD ⟶
      (G ⋙ F) ⋙ CategoryTheory.shiftFunctor Y (1 : ℤ) :=
  (P.counitFirstMapNormalizationData K).normalizedThird

/-- The presented ordinary counit triangle
`G F ⟶ 𝟭 Y ⟶ transportedTwist ⟶ (G F)⟦1⟧`. -/
noncomputable def presentedCounitTriangle : Y ⥤ Triangle Y :=
  (P.counitFirstMapNormalizationData K).normalizedTriangle

@[simp]
theorem presentedCounitTriangle_obj₁ (Z : Y) :
    ((P.presentedCounitTriangle K).obj Z).obj₁ = (G ⋙ F).obj Z :=
  rfl

@[simp]
theorem presentedCounitTriangle_obj₂ (Z : Y) :
    ((P.presentedCounitTriangle K).obj Z).obj₂ = Z :=
  rfl

@[simp]
theorem presentedCounitTriangle_obj₃ (Z : Y) :
    ((P.presentedCounitTriangle K).obj Z).obj₃ =
      (K.transportedTwist eD).obj Z :=
  rfl

@[simp]
theorem presentedCounitTriangle_mor₁ (Z : Y) :
    ((P.presentedCounitTriangle K).obj Z).mor₁ =
      (P.toAdjunction A).counit.app Z :=
  rfl

@[simp]
theorem presentedCounitTriangle_mor₂ (Z : Y) :
    ((P.presentedCounitTriangle K).obj Z).mor₂ =
      (P.counitToTransportedTwist K).app Z :=
  rfl

@[simp]
theorem presentedCounitTriangle_mor₃ (Z : Y) :
    ((P.presentedCounitTriangle K).obj Z).mor₃ =
      (P.transportedTwistToShiftedComposite K).app Z :=
  rfl

/-- The raw transported dg counit triangle and its presented form are
naturally isomorphic. -/
noncomputable def rawTransportedTwistTriangleIsoPresented :
    K.rawTransportedTwistTriangle (eD := eD) ≅ P.presentedCounitTriangle K :=
  (P.counitFirstMapNormalizationData K).rawIsoNormalized

@[simp]
theorem rawTransportedTwistTriangleIsoPresented_hom_app_hom₁ (Z : Y) :
    ((P.rawTransportedTwistTriangleIsoPresented K).hom.app Z).hom₁ =
      (P.counitTriangleObj₁Iso K).hom.app Z :=
  rfl

@[simp]
theorem rawTransportedTwistTriangleIsoPresented_hom_app_hom₂ (Z : Y) :
    ((P.rawTransportedTwistTriangleIsoPresented K).hom.app Z).hom₂ =
      (K.rawTransportedTwistTriangleObj₂Iso (eD := eD)).hom.app Z :=
  rfl

@[simp]
theorem rawTransportedTwistTriangleIsoPresented_hom_app_hom₃ (Z : Y) :
    ((P.rawTransportedTwistTriangleIsoPresented K).hom.app Z).hom₃ = 𝟙 _ :=
  rfl

section Distinguished

variable [Limits.HasZeroObject Y] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]
  [eD.functor.IsTriangulated]

/-- Every value of the presented ordinary counit triangle is distinguished. -/
theorem presentedCounitTriangle_obj_distinguished (Z : Y) :
    (P.presentedCounitTriangle K).obj Z ∈ distTriang Y :=
  (P.counitFirstMapNormalizationData K).normalizedTriangle_obj_distinguished
    (K.rawTransportedTwistTriangle_obj_distinguished (eD := eD)) Z

end Distinguished

end H0Presentation

namespace H0Presentation

variable [IsPretriangulated C] [HasShift X ℤ]
  [eC.functor.CommShift ℤ]
  (P : H0Presentation (L := L) (R := R) eC eD F G)
  (K : A.UnitConeData)

/-- The second projection of the raw transported dg unit triangle, identified
with the composite of the named presented left and right adjoints. -/
noncomputable def unitTriangleObj₂Iso :
    K.rawTransportedUnitTriangle (eC := eC) ⋙ Triangle.π₂ ≅ F ⋙ G := by
  let right₀ := transportedH0Right (R := R) eC eD
  exact
    Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft eC.inverse (DGFunctor.h0CompIso L R))
        eC.functor ≪≫
      Functor.associator eC.inverse (L.h0 ⋙ R.h0) eC.functor ≪≫
      Functor.isoWhiskerLeft eC.inverse
        (Functor.associator L.h0 R.h0 eC.functor) ≪≫
      (Functor.associator eC.inverse L.h0
        (R.h0 ⋙ eC.functor)).symm ≪≫
      Functor.isoWhiskerLeft (eC.inverse ⋙ L.h0)
        (eD.funInvIdAssoc (R.h0 ⋙ eC.functor)).symm ≪≫
      (Functor.associator (eC.inverse ⋙ L.h0) eD.functor
        (eD.inverse ⋙ (R.h0 ⋙ eC.functor))).symm ≪≫
      Functor.isoWhiskerRight P.leftIso right₀ ≪≫
      Functor.isoWhiskerLeft F P.rightIso

private noncomputable def unitTargetUnitApp (Z : X) :
    (K.rawTransportedUnitTriangle (eC := eC) ⋙ Triangle.π₂).obj Z ⟶
      (transportedH0Right (R := R) eC eD).obj
        ((transportedH0Left (L := L) eC eD).obj Z) :=
  eC.functor.map
    (R.h0.map (eD.unit.app (L.h0.obj (eC.inverse.obj Z))))

private noncomputable def presentedUnitTailApp (Z : X) :
    (transportedH0Right (R := R) eC eD).obj
        ((transportedH0Left (L := L) eC eD).obj Z) ⟶
      (F ⋙ G).obj Z :=
  (transportedH0Right (R := R) eC eD).map (P.leftIso.hom.app Z) ≫
    P.rightIso.hom.app (F.obj Z)

private noncomputable def presentedObj₂IsoHomApp (Z : X) :
    (K.rawTransportedUnitTriangle (eC := eC) ⋙ Triangle.π₂).obj Z ⟶
      (F ⋙ G).obj Z :=
  unitTargetUnitApp (L := L) (R := R) (eC := eC) (eD := eD) K Z ≫
    presentedUnitTailApp (L := L) (R := R) (eC := eC) (eD := eD) P Z

private theorem unitTriangleObj₂Iso_hom_app (Z : X) :
    (P.unitTriangleObj₂Iso K).hom.app Z =
      presentedObj₂IsoHomApp (L := L) (R := R) (eC := eC) (eD := eD)
        P K Z := by
  simp only [unitTriangleObj₂Iso, Iso.trans_hom, NatTrans.comp_app]
  rw [whiskeredH0CompIso_hom_app (L := R) (R := L) (eD := eC)]
  simp
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  erw [Category.id_comp]
  rfl

private noncomputable def transportedUnitApp (Z : X) :
    (K.rawTransportedUnitTriangle (eC := eC) ⋙ Triangle.π₁).obj Z ⟶
      (transportedH0Right (R := R) eC eD).obj
        ((transportedH0Left (L := L) eC eD).obj Z) :=
  ((K.rawTransportedUnitTriangle (eC := eC)).obj Z).mor₁ ≫
    unitTargetUnitApp (L := L) (R := R) (eC := eC) (eD := eD) K Z

private noncomputable def presentedTransportedUnitApp (Z : X) :
    (K.rawTransportedUnitTriangle (eC := eC) ⋙ Triangle.π₁).obj Z ⟶
      (F ⋙ G).obj Z :=
  transportedUnitApp (L := L) (R := R) (A := A) (eC := eC) (eD := eD)
      K Z ≫
    presentedUnitTailApp (L := L) (R := R) (eC := eC) (eD := eD) P Z

private theorem rawTransportedUnitTriangle_mor₁_comp_obj₂Iso_hom_app
    (Z : X) :
    (Functor.whiskerLeft (K.rawTransportedUnitTriangle (eC := eC))
          Triangle.π₁Toπ₂).app Z ≫
        (P.unitTriangleObj₂Iso K).hom.app Z =
      presentedTransportedUnitApp
        (L := L) (R := R) (eC := eC) (eD := eD) P K Z := by
  change ((K.rawTransportedUnitTriangle (eC := eC)).obj Z).mor₁ ≫
      (P.unitTriangleObj₂Iso K).hom.app Z = _
  rw [P.unitTriangleObj₂Iso_hom_app]
  unfold presentedObj₂IsoHomApp presentedTransportedUnitApp transportedUnitApp
  exact (Category.assoc _ _ _).symm

private noncomputable def presentedUnitApp (Z : X) :
    (𝟭 X).obj Z ⟶ (F ⋙ G).obj Z :=
  (A.transportedH0 eC eD).unit.app Z ≫
    presentedUnitTailApp (L := L) (R := R) (eC := eC) (eD := eD) P Z

omit [IsPretriangulated C] [HasShift X ℤ] [eC.functor.CommShift ℤ] in
private theorem toAdjunction_unit_app_eq_presentedUnitApp (Z : X) :
    (P.toAdjunction A).unit.app Z =
      presentedUnitApp (A := A) (eC := eC) (eD := eD) P Z := by
  rw [P.toAdjunction_unit_app A]
  unfold presentedUnitApp presentedUnitTailApp
  rfl

@[reassoc]
private theorem obj₁Iso_hom_comp_transportedH0_unit (Z : X) :
    (K.rawTransportedUnitTriangleObj₁Iso (eC := eC)).hom.app Z ≫
        (A.transportedH0 eC eD).unit.app Z =
      transportedUnitApp (L := L) (R := R) (A := A) (eC := eC) (eD := eD)
        K Z := by
  rw [K.rawTransportedUnitTriangleObj₁Iso_hom_app]
  unfold transportedUnitApp unitTargetUnitApp
  rw [A.transportedH0_unit_app eC eD]
  simp only [Equivalence.symm_unit, Equivalence.toAdjunction_unit,
    Category.assoc]
  let i := eC.counitIso.app Z
  change i.hom ≫ i.inv ≫
      eC.functor.map (A.h0Unit.app (eC.inverse.obj Z)) ≫
        eC.functor.map
          (R.h0.map (eD.unit.app (L.h0.obj (eC.inverse.obj Z)))) = _
  rw [Iso.hom_inv_id_assoc]
  rw [K.rawTransportedUnitTriangle_obj_mor₁]
  rfl

private theorem obj₁Iso_hom_comp_presentedUnit (Z : X) :
    (K.rawTransportedUnitTriangleObj₁Iso (eC := eC)).hom.app Z ≫
        (P.toAdjunction A).unit.app Z =
      presentedTransportedUnitApp
        (L := L) (R := R) (eC := eC) (eD := eD) P K Z := by
  rw [P.toAdjunction_unit_app_eq_presentedUnitApp]
  unfold presentedUnitApp presentedTransportedUnitApp
  exact obj₁Iso_hom_comp_transportedH0_unit_assoc (K := K) (Z := Z)
    (presentedUnitTailApp (L := L) (R := R) (eC := eC) (eD := eD) P Z)

/-- The generic first-map normalization data for the transported dg unit
triangle.  Its named first map is exactly the unit of the ordinary adjunction
constructed by `P`. -/
noncomputable def unitFirstMapNormalizationData :
    Triangle.FirstMapNormalizationData
      (K.rawTransportedUnitTriangle (eC := eC)) (𝟭 X) (F ⋙ G)
        (P.toAdjunction A).unit where
  obj₁Iso := K.rawTransportedUnitTriangleObj₁Iso (eC := eC)
  obj₂Iso := P.unitTriangleObj₂Iso K
  square := by
    ext Z
    simp only [NatTrans.comp_app]
    rw [P.rawTransportedUnitTriangle_mor₁_comp_obj₂Iso_hom_app K,
      P.obj₁Iso_hom_comp_presentedUnit K]

/-- The second map of the presented unit triangle, from the adjunction
composite to the transported unshifted unit cone. -/
noncomputable def compositeToTransportedUnitCone :
    F ⋙ G ⟶ K.transportedUnitCone eC :=
  (P.unitFirstMapNormalizationData K).normalizedSecond

/-- The connecting map of the presented unit triangle, from the transported
unshifted unit cone to the shift of the identity. -/
noncomputable def transportedUnitConeToShiftedIdentity :
    K.transportedUnitCone eC ⟶
      𝟭 X ⋙ CategoryTheory.shiftFunctor X (1 : ℤ) :=
  (P.unitFirstMapNormalizationData K).normalizedThird

/-- The presented ordinary unit triangle
`𝟭 X ⟶ F G ⟶ transportedUnitCone ⟶ (𝟭 X)⟦1⟧`. -/
noncomputable def presentedUnitTriangle : X ⥤ Triangle X :=
  (P.unitFirstMapNormalizationData K).normalizedTriangle

@[simp]
theorem presentedUnitTriangle_obj₁ (Z : X) :
    ((P.presentedUnitTriangle K).obj Z).obj₁ = Z :=
  rfl

@[simp]
theorem presentedUnitTriangle_obj₂ (Z : X) :
    ((P.presentedUnitTriangle K).obj Z).obj₂ = (F ⋙ G).obj Z :=
  rfl

@[simp]
theorem presentedUnitTriangle_obj₃ (Z : X) :
    ((P.presentedUnitTriangle K).obj Z).obj₃ =
      (K.transportedUnitCone eC).obj Z :=
  rfl

@[simp]
theorem presentedUnitTriangle_mor₁ (Z : X) :
    ((P.presentedUnitTriangle K).obj Z).mor₁ =
      (P.toAdjunction A).unit.app Z :=
  rfl

@[simp]
theorem presentedUnitTriangle_mor₂ (Z : X) :
    ((P.presentedUnitTriangle K).obj Z).mor₂ =
      (P.compositeToTransportedUnitCone K).app Z :=
  rfl

@[simp]
theorem presentedUnitTriangle_mor₃ (Z : X) :
    ((P.presentedUnitTriangle K).obj Z).mor₃ =
      (P.transportedUnitConeToShiftedIdentity K).app Z :=
  rfl

/-- The raw transported dg unit triangle and its presented form are naturally
isomorphic. -/
noncomputable def rawTransportedUnitTriangleIsoPresented :
    K.rawTransportedUnitTriangle (eC := eC) ≅ P.presentedUnitTriangle K :=
  (P.unitFirstMapNormalizationData K).rawIsoNormalized

@[simp]
theorem rawTransportedUnitTriangleIsoPresented_hom_app_hom₁ (Z : X) :
    ((P.rawTransportedUnitTriangleIsoPresented K).hom.app Z).hom₁ =
      (K.rawTransportedUnitTriangleObj₁Iso (eC := eC)).hom.app Z :=
  rfl

@[simp]
theorem rawTransportedUnitTriangleIsoPresented_hom_app_hom₂ (Z : X) :
    ((P.rawTransportedUnitTriangleIsoPresented K).hom.app Z).hom₂ =
      (P.unitTriangleObj₂Iso K).hom.app Z :=
  rfl

@[simp]
theorem rawTransportedUnitTriangleIsoPresented_hom_app_hom₃ (Z : X) :
    ((P.rawTransportedUnitTriangleIsoPresented K).hom.app Z).hom₃ = 𝟙 _ :=
  rfl

section Distinguished

variable [Limits.HasZeroObject X] [Preadditive X]
  [∀ n : ℤ, (shiftFunctor X n).Additive] [Pretriangulated X]
  [eC.functor.IsTriangulated]

/-- Every value of the presented ordinary unit triangle is distinguished. -/
theorem presentedUnitTriangle_obj_distinguished (Z : X) :
    (P.presentedUnitTriangle K).obj Z ∈ distTriang X :=
  (P.unitFirstMapNormalizationData K).normalizedTriangle_obj_distinguished
    (K.rawTransportedUnitTriangle_obj_distinguished (eC := eC)) Z

end Distinguished

end H0Presentation

end DGAdjunction

end CategoryTheory
