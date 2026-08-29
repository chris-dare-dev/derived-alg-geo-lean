/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePseudofunctor

/-!
# Coherent affine pullback on the bounded-projective derived locus

The affine bounded-projective homotopy pseudofunctor is transported through
the localization equivalences onto its essential image in the derived
category.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Bicategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

private def qhTransportFunctor
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁) (F : C₀ ⥤ C₁) :
    D₀ ⥤ D₁ :=
  E₀.inverse ⋙ F ⋙ E₁.functor

private def qhTransportCompIso
    {C₀ D₀ C₁ D₁ C₂ D₂ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    [Category C₂] [Category D₂]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (e : F ⋙ G ≅ H) :
    qhTransportFunctor E₀ E₁ F ⋙ qhTransportFunctor E₁ E₂ G ≅
      qhTransportFunctor E₀ E₂ H := by
  let cancelE₁ : E₁.functor ⋙ (E₁.inverse ⋙ G) ≅ G :=
    (Functor.associator E₁.functor E₁.inverse G).symm ≪≫
      Functor.isoWhiskerRight E₁.unitIso.symm G ≪≫ G.leftUnitor
  change (E₀.inverse ⋙ F ⋙ E₁.functor) ⋙
      (E₁.inverse ⋙ G ⋙ E₂.functor) ≅
    E₀.inverse ⋙ H ⋙ E₂.functor
  exact
    (Functor.associator (E₀.inverse ⋙ F ⋙ E₁.functor)
      (E₁.inverse ⋙ G) E₂.functor).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator (E₀.inverse ⋙ F) E₁.functor
        (E₁.inverse ⋙ G)) E₂.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (E₀.inverse ⋙ F) cancelE₁) E₂.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.associator E₀.inverse F G) E₂.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft E₀.inverse e) E₂.functor

private def qhTransportIdIso
    {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) (F G : C ⥤ C) (e₀ : F ≅ G) (e₁ : G ≅ 𝟭 C) :
    qhTransportFunctor E E F ≅ 𝟭 D :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft E.inverse e₀) E.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft E.inverse e₁) E.functor ≪≫
    Functor.isoWhiskerRight (Functor.rightUnitor E.inverse) E.functor ≪≫
    E.counitIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem qhTransport_associativity
    {C₀ D₀ C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    [Category C₂] [Category D₂] [Category C₃] [Category D₃]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁)
    (E₂ : C₂ ≌ D₂) (E₃ : C₃ ≌ D₃)
    (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₂₃ : C₂ ⥤ C₃)
    (F₀₂ : C₀ ⥤ C₂) (F₁₃ : C₁ ⥤ C₃) (F₀₃ : C₀ ⥤ C₃)
    (c₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (c₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃)
    (c₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃) (c₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃)
    (hassoc : c₀₂₃.symm.hom ≫ Functor.whiskerRight c₀₁₂.symm.hom F₂₃ ≫
      (Functor.associator F₀₁ F₁₂ F₂₃).hom ≫
      Functor.whiskerLeft F₀₁ c₁₂₃.hom ≫ c₀₁₃.hom = 𝟙 _) :
    (qhTransportCompIso E₀ E₂ E₃ F₀₂ F₂₃ F₀₃ c₀₂₃).symm.hom ≫
      Functor.whiskerRight
        (qhTransportCompIso E₀ E₁ E₂ F₀₁ F₁₂ F₀₂ c₀₁₂).symm.hom _ ≫
      (Functor.associator
        (qhTransportFunctor E₀ E₁ F₀₁)
        (qhTransportFunctor E₁ E₂ F₁₂)
        (qhTransportFunctor E₂ E₃ F₂₃)).hom ≫
      Functor.whiskerLeft (qhTransportFunctor E₀ E₁ F₀₁)
        (qhTransportCompIso E₁ E₂ E₃ F₁₂ F₂₃ F₁₃ c₁₂₃).hom ≫
      (qhTransportCompIso E₀ E₁ E₃ F₀₁ F₁₃ F₀₃ c₀₁₃).hom =
        𝟙 _ := by
  apply NatTrans.ext
  funext K
  have hCompNaturality := c₁₂₃.hom.naturality
    (E₁.unitIso.hom.app (F₀₁.obj (E₀.inverse.obj K)))
  dsimp at hCompNaturality
  have hCore := NatTrans.congr_app hassoc (E₀.inverse.obj K)
  simp at hCore
  apply E₃.inverse.map_injective
  dsimp [qhTransportCompIso, qhTransportFunctor]
  simp [Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Functor.map_id, Category.assoc]
  slice_lhs 4 5 => rw [hCompNaturality]
  simp [Category.assoc]
  slice_lhs 2 5 => rw [hCore]
  simpa only [Category.id_comp] using
    E₃.unitIso_inv_hom_id_app (F₀₃.obj (E₀.inverse.obj K))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem qhTransport_leftUnitality
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁)
    (Fid Gid : C₀ ⥤ C₀) (F : C₀ ⥤ C₁)
    (e₀ : Fid ≅ Gid) (e₁ : Gid ≅ 𝟭 C₀) (c : Fid ⋙ F ≅ F)
    (hleft : c.symm.hom ≫ Functor.whiskerRight (e₀ ≪≫ e₁).hom F ≫
      (Functor.leftUnitor F).hom = 𝟙 _) :
    (qhTransportCompIso E₀ E₀ E₁ Fid F F c).symm.hom ≫
      Functor.whiskerRight (qhTransportIdIso E₀ Fid Gid e₀ e₁).hom
        (qhTransportFunctor E₀ E₁ F) ≫
      (Functor.leftUnitor (qhTransportFunctor E₀ E₁ F)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext K
  have hCore := NatTrans.congr_app hleft (E₀.inverse.obj K)
  simp at hCore
  apply E₁.inverse.map_injective
  dsimp [qhTransportCompIso, qhTransportIdIso, qhTransportFunctor]
  simp [Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Functor.map_id, Category.assoc]
  slice_lhs 2 4 => rw [hCore]
  simpa only [Category.id_comp] using
    E₁.unitIso_inv_hom_id_app (F.obj (E₀.inverse.obj K))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem qhTransport_rightUnitality
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁)
    (F : C₀ ⥤ C₁) (Fid Gid : C₁ ⥤ C₁)
    (e₀ : Fid ≅ Gid) (e₁ : Gid ≅ 𝟭 C₁) (c : F ⋙ Fid ≅ F)
    (hright : c.symm.hom ≫ Functor.whiskerLeft F (e₀ ≪≫ e₁).hom ≫
      (Functor.rightUnitor F).hom = 𝟙 _) :
    (qhTransportCompIso E₀ E₁ E₁ F Fid F c).symm.hom ≫
      Functor.whiskerLeft (qhTransportFunctor E₀ E₁ F)
        (qhTransportIdIso E₁ Fid Gid e₀ e₁).hom ≫
      (Functor.rightUnitor (qhTransportFunctor E₀ E₁ F)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext K
  have hCore := NatTrans.congr_app hright (E₀.inverse.obj K)
  simp at hCore
  apply E₁.inverse.map_injective
  dsimp [qhTransportCompIso, qhTransportIdIso, qhTransportFunctor]
  simp [Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Functor.map_id, Category.assoc]
  slice_lhs 2 4 => rw [hCore]
  simpa only [Category.id_comp] using
    E₁.unitIso_inv_hom_id_app (F.obj (E₀.inverse.obj K))

private def affineHomotopyUnitComparison (R : CommRingCat.{u}) :
    affineBoundedAboveProjectiveHomotopyPullback (𝟙 R : R ⟶ R) ≅
      mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)) :=
  mapBoundedAboveProjectiveHomotopyIso
    (ModuleCat.extendScalars.{u, u, u} (𝟙 R : R ⟶ R).hom)
    (𝟭 (ModuleCat R))
    (by simpa using ModuleCat.extendScalarsId R)

private def affineHomotopyUnitIdComparison (R : CommRingCat.{u}) :
    mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)) ≅
      𝟭 (BoundedAboveProjectiveHomotopyCategory (ModuleCat R)) :=
  mapBoundedAboveProjectiveHomotopyIdIso (ModuleCat R)

private theorem affineDerivedPullback_eq_qhTransport
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    affineBoundedAboveProjectiveDerivedPullback f =
      qhTransportFunctor
        (boundedAboveProjectiveQhEquivalence (ModuleCat R))
        (boundedAboveProjectiveQhEquivalence (ModuleCat A))
        (affineBoundedAboveProjectiveHomotopyPullback f) :=
  rfl

private theorem affineDerivedPullbackCompIso_eq_qhTransport
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineBoundedAboveProjectiveDerivedPullbackCompIso f g =
      qhTransportCompIso
        (boundedAboveProjectiveQhEquivalence (ModuleCat R))
        (boundedAboveProjectiveQhEquivalence (ModuleCat A))
        (boundedAboveProjectiveQhEquivalence (ModuleCat B))
        (affineBoundedAboveProjectiveHomotopyPullback f)
        (affineBoundedAboveProjectiveHomotopyPullback g)
        (affineBoundedAboveProjectiveHomotopyPullback (f ≫ g))
        (affineBoundedAboveProjectiveHomotopyPullbackCompIso f g) :=
  rfl

private theorem affineDerivedPullbackIdIso_eq_qhTransport
    (R : CommRingCat.{u}) :
    affineBoundedAboveProjectiveDerivedPullbackIdIso R =
      qhTransportIdIso
        (boundedAboveProjectiveQhEquivalence (ModuleCat R))
        (affineBoundedAboveProjectiveHomotopyPullback (𝟙 R : R ⟶ R))
        (mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)))
        (affineHomotopyUnitComparison R)
        (affineHomotopyUnitIdComparison R) :=
  rfl

/-- The supported affine derived compositor satisfies the pentagon equation. -/
theorem affineBoundedAboveProjectiveDerivedPullback_associativity
    {R A B C : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) (h : B ⟶ C) :
    (affineBoundedAboveProjectiveDerivedPullbackCompIso (f ≫ g) h).symm.hom ≫
      Functor.whiskerRight
        (affineBoundedAboveProjectiveDerivedPullbackCompIso f g).symm.hom _ ≫
      (Functor.associator
        (affineBoundedAboveProjectiveDerivedPullback f)
        (affineBoundedAboveProjectiveDerivedPullback g)
        (affineBoundedAboveProjectiveDerivedPullback h)).hom ≫
      Functor.whiskerLeft (affineBoundedAboveProjectiveDerivedPullback f)
        (affineBoundedAboveProjectiveDerivedPullbackCompIso g h).hom ≫
      (affineBoundedAboveProjectiveDerivedPullbackCompIso f (g ≫ h)).hom =
        𝟙 _ := by
  exact qhTransport_associativity
      (boundedAboveProjectiveQhEquivalence (ModuleCat R))
      (boundedAboveProjectiveQhEquivalence (ModuleCat A))
      (boundedAboveProjectiveQhEquivalence (ModuleCat B))
      (boundedAboveProjectiveQhEquivalence (ModuleCat C))
      (affineBoundedAboveProjectiveHomotopyPullback f)
      (affineBoundedAboveProjectiveHomotopyPullback g)
      (affineBoundedAboveProjectiveHomotopyPullback h)
      (affineBoundedAboveProjectiveHomotopyPullback (f ≫ g))
      (affineBoundedAboveProjectiveHomotopyPullback (g ≫ h))
      (affineBoundedAboveProjectiveHomotopyPullback ((f ≫ g) ≫ h))
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso f g)
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso g h)
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso (f ≫ g) h)
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (g ≫ h))
      (affineBoundedAboveProjectiveHomotopyPullback_associativity f g h)

private theorem affineHomotopyPullback_leftUnitality_twoStage
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso (𝟙 R) f).symm.hom ≫
      Functor.whiskerRight
        ((affineHomotopyUnitComparison R ≪≫
            affineHomotopyUnitIdComparison R)).hom
        (affineBoundedAboveProjectiveHomotopyPullback f) ≫
      (Functor.leftUnitor
        (affineBoundedAboveProjectiveHomotopyPullback f)).hom = 𝟙 _ := by
  exact affineBoundedAboveProjectiveHomotopyPullback_leftUnitality f

private theorem affineHomotopyPullback_rightUnitality_twoStage
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (𝟙 A)).symm.hom ≫
      Functor.whiskerLeft
        (affineBoundedAboveProjectiveHomotopyPullback f)
        ((affineHomotopyUnitComparison A ≪≫
            affineHomotopyUnitIdComparison A)).hom ≫
      (Functor.rightUnitor
        (affineBoundedAboveProjectiveHomotopyPullback f)).hom = 𝟙 _ := by
  exact affineBoundedAboveProjectiveHomotopyPullback_rightUnitality f

set_option linter.defProp false in
private def affineQhTransport_leftUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :=
  qhTransport_leftUnitality
    (boundedAboveProjectiveQhEquivalence (ModuleCat R))
    (boundedAboveProjectiveQhEquivalence (ModuleCat A))
    (affineBoundedAboveProjectiveHomotopyPullback (𝟙 R : R ⟶ R))
    (mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)))
    (affineBoundedAboveProjectiveHomotopyPullback f)
    (affineHomotopyUnitComparison R)
    (affineHomotopyUnitIdComparison R)
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso (𝟙 R) f)
    (affineHomotopyPullback_leftUnitality_twoStage f)

/-- The supported affine derived compositor and unit satisfy the left
triangle equation. -/
theorem affineBoundedAboveProjectiveDerivedPullback_leftUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveDerivedPullbackCompIso (𝟙 R) f).symm.hom ≫
      Functor.whiskerRight
        (affineBoundedAboveProjectiveDerivedPullbackIdIso R).hom _ ≫
      (Functor.leftUnitor
        (affineBoundedAboveProjectiveDerivedPullback f)).hom = 𝟙 _ := by
  simp only [affineDerivedPullbackCompIso_eq_qhTransport,
    affineDerivedPullbackIdIso_eq_qhTransport,
    affineDerivedPullback_eq_qhTransport]
  exact affineQhTransport_leftUnitality f

set_option linter.defProp false in
private def affineQhTransport_rightUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :=
  qhTransport_rightUnitality
    (boundedAboveProjectiveQhEquivalence (ModuleCat R))
    (boundedAboveProjectiveQhEquivalence (ModuleCat A))
    (affineBoundedAboveProjectiveHomotopyPullback f)
    (affineBoundedAboveProjectiveHomotopyPullback (𝟙 A : A ⟶ A))
    (mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat A)))
    (affineHomotopyUnitComparison A)
    (affineHomotopyUnitIdComparison A)
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (𝟙 A))
    (affineHomotopyPullback_rightUnitality_twoStage f)

/-- The supported affine derived compositor and unit satisfy the right
triangle equation. -/
theorem affineBoundedAboveProjectiveDerivedPullback_rightUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveDerivedPullbackCompIso f (𝟙 A)).symm.hom ≫
      Functor.whiskerLeft (affineBoundedAboveProjectiveDerivedPullback f)
        (affineBoundedAboveProjectiveDerivedPullbackIdIso A).hom ≫
      (Functor.rightUnitor
        (affineBoundedAboveProjectiveDerivedPullback f)).hom = 𝟙 _ := by
  simp only [affineDerivedPullbackCompIso_eq_qhTransport,
    affineDerivedPullbackIdIso_eq_qhTransport,
    affineDerivedPullback_eq_qhTransport]
  exact affineQhTransport_rightUnitality f

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary affine pullback on the bounded-above projective derived loci,
packaged with its transported unit, compositor, pentagon, and triangle
equations. -/
def affineBoundedAboveProjectiveDerivedPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u + 1, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of
      (BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R)))
    (fun f ↦ (affineBoundedAboveProjectiveDerivedPullback f).toCatHom)
    (fun R ↦ Cat.Hom.isoMk
      (affineBoundedAboveProjectiveDerivedPullbackIdIso R))
    (fun f g ↦ Cat.Hom.isoMk
      (affineBoundedAboveProjectiveDerivedPullbackCompIso f g).symm) ?_ ?_ ?_
  · intros R A B C f g h
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveDerivedPullback_associativity f g h) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveDerivedPullback_leftUnitality f) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveDerivedPullback_rightUnitality f) K

end

end CategoryTheory.Triangulated.StabilityCondition.Families
