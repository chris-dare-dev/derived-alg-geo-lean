/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.CategoryTheory.Whiskering

/-!
# Lifting bifunctors to full subcategories

If a bifunctor preserves an object property in two inputs satisfying that property, it restricts
to the corresponding full subcategory in both variables. The construction below is the
two-variable analogue of Mathlib's `ObjectProperty.lift`.

## Main results

`CategoryTheory.ObjectProperty.lift₂CommShift₂Int` transports the ambient `CommShift₂Int`
structure, including its Koszul compatibility, through `lift₂` when the property is shift-stable.
It returns explicit data rather than a global instance, avoiding instance diamonds between
independent restrictions.
-/

namespace CategoryTheory.ObjectProperty

universe v v' u u'

variable {C : Type u} [Category.{v} C]

/-- Restrict a bifunctor to a full subcategory when it preserves the defining property in both
variables. -/
@[simps]
def lift₂ (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ X Y, P X → P Y → P ((F.obj X).obj Y)) :
    P.FullSubcategory ⥤ P.FullSubcategory ⥤ P.FullSubcategory where
  obj X := P.lift (P.ι ⋙ F.obj X.obj) (fun Y ↦ hF X.obj Y.obj X.property Y.property)
  map {X Y} f :=
    { app := fun Z ↦ homMk ((F.map f.hom).app Z.obj)
      naturality := fun {Z W} g ↦ by
        apply P.hom_ext
        exact (F.map f.hom).naturality g.hom }
  map_id X := by
    ext Y
    simp
    rfl
  map_comp f g := by
    ext Y
    simp
    rfl

/-- Forgetting the output of `lift₂` recovers the original bifunctor restricted along the
inclusion in both inputs. This is definitionally an identity isomorphism. -/
def lift₂CompιIso (P : ObjectProperty C) (F : C ⥤ C ⥤ C)
    (hF : ∀ X Y, P X → P Y → P ((F.obj X).obj Y)) :
    P.lift₂ F hF ⋙ (Functor.whiskeringRight _ _ _).obj P.ι ≅
      P.ι ⋙ F ⋙ (Functor.whiskeringLeft _ _ _).obj P.ι :=
  Iso.refl _

private noncomputable def liftNatTrans {C : Type*} [Category* C]
    {E : Type*} [Category* E] (P : ObjectProperty C)
    {F G : E ⥤ C} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (τ : F ⟶ G) : P.lift F hF ⟶ P.lift G hG where
  app X := homMk (τ.app X)
  naturality := fun {X Y} f => by
    apply P.hom_ext
    exact τ.naturality f

set_option backward.isDefEq.respectTransparency false in
private lemma commShift_of_whiskerRight
    {D E E' : Type*} [Category* D] [Category* E] [Category* E']
    {A : Type*} [AddMonoid A]
    [HasShift E A] [HasShift D A] [HasShift E' A]
    {F G : E ⥤ D} (H : D ⥤ E') [H.Faithful]
    [F.CommShift A] [G.CommShift A] [H.CommShift A]
    (τ : F ⟶ G) [NatTrans.CommShift (Functor.whiskerRight τ H) A] :
    NatTrans.CommShift τ A := by
  apply NatTrans.CommShift.of_core
  intro a
  constructor
  ext X
  apply H.map_injective
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp]
  change
    H.map ((F.commShiftIso a).hom.app X) ≫
      H.map ((shiftFunctor D a).map (τ.app X)) =
    H.map (τ.app (X⟦a⟧)) ≫ H.map ((G.commShiftIso a).hom.app X)
  apply (cancel_mono ((H.commShiftIso a).hom.app (G.obj X))).mp
  rw [Category.assoc, Functor.commShiftIso_hom_naturality]
  have h := NatTrans.shift_app_comm (Functor.whiskerRight τ H) a X
  simpa only [Category.assoc, Functor.commShiftIso_comp_hom_app, Functor.comp_obj,
    Functor.whiskerRight_app] using h

private lemma liftNatTrans_commShift
    {C : Type*} [Category* C] {E : Type*} [Category* E]
    {A : Type*} [AddMonoid A] [HasShift C A] [HasShift E A]
    (P : ObjectProperty C) [P.IsStableUnderShift A]
    {F G : E ⥤ C} (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (τ : F ⟶ G) [F.CommShift A] [G.CommShift A] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (liftNatTrans P hF hG τ) A := by
  letI : P.ι.CommShift A := P.commShiftι
  letI : (P.lift F hF).CommShift A :=
    Functor.CommShift.ofComp (P.liftCompιIso F hF) A
  letI : (P.lift G hG).CommShift A :=
    Functor.CommShift.ofComp (P.liftCompιIso G hG) A
  have hwhisker : NatTrans.CommShift
      (Functor.whiskerRight (liftNatTrans P hF hG τ) P.ι) A := by
    suffices hEq : Functor.whiskerRight (liftNatTrans P hF hG τ) P.ι =
        (P.liftCompιIso F hF).hom ≫ τ ≫ (P.liftCompιIso G hG).inv by
      rw [hEq]
      infer_instance
    ext X
    simp [liftNatTrans, ObjectProperty.liftCompιIso, ObjectProperty.lift,
      ObjectProperty.ι]
    change τ.app X = 𝟙 (F.obj X) ≫ τ.app X ≫ 𝟙 (G.obj X)
    simp
  exact commShift_of_whiskerRight (H := P.ι) (liftNatTrans P hF hG τ)

private def liftOutput {D E : Type*} [Category* D] [Category* E]
    {C : Type*} [Category* C] (P : ObjectProperty C) (G : D ⥤ E ⥤ C)
    (hG : ∀ X Y, P ((G.obj X).obj Y)) : D ⥤ E ⥤ P.FullSubcategory where
  obj X := P.lift (G.obj X) (hG X)
  map {X Y} f :=
    { app := fun Z => homMk ((G.map f).app Z)
      naturality := fun {Z W} g => by
        apply P.hom_ext
        exact (G.map f).naturality g }

unseal ObjectProperty.hasShift in
private lemma iota_map_shiftFunctor_map
    {C : Type*} [Category* C] {A : Type*} [AddMonoid A] [HasShift C A]
    (P : ObjectProperty C) [P.IsStableUnderShift A]
    {X Y : P.FullSubcategory} (f : X ⟶ Y) (a : A) :
    P.ι.map ((shiftFunctor P.FullSubcategory a).map f) =
      (shiftFunctor C a).map (P.ι.map f) := by
  rfl

unseal ObjectProperty.hasShift ObjectProperty.commShiftι in
private lemma iota_map_lift_commShift_hom {D : Type*} [Category* D]
    {C : Type*} [Category* C] {A : Type*} [AddMonoid A] [HasShift D A] [HasShift C A]
    (P : ObjectProperty C) [P.IsStableUnderShift A]
    (L : D ⥤ C) (hL : ∀ X, P (L.obj X)) [L.CommShift A]
    (X : D) (a : A) :
    P.ι.map (((P.lift L hL).commShiftIso a).hom.app X) =
      (L.commShiftIso a).hom.app X := by
  letI : HasShift P.FullSubcategory A := P.hasShift
  letI : P.ι.CommShift A := P.commShiftι
  letI : (P.lift L hL).CommShift A :=
    Functor.CommShift.ofComp (P.liftCompιIso L hL) A
  change P.ι.map
    ((Functor.CommShift.OfComp.iso (P.liftCompιIso L hL) a).hom.app X) = _
  rw [Functor.CommShift.OfComp.map_iso_hom_app]
  rw [show P.ι.commShiftIso a =
    P.liftCompιIso (P.ι ⋙ shiftFunctor C a)
      (fun Z => P.le_shift a _ Z.property) from rfl]
  unfold ObjectProperty.liftCompιIso
  erw [Category.id_comp, Functor.map_id, Category.comp_id]
  erw [Category.comp_id]

unseal ObjectProperty.hasShift ObjectProperty.commShiftι in
private lemma iota_map_shiftComm_hom {C : Type*} [Category* C] {A : Type*}
    [AddCommMonoid A] [HasShift C A]
    (P : ObjectProperty C) [P.IsStableUnderShift A]
    (X : P.FullSubcategory) (a b : A) :
    P.ι.map ((shiftFunctorComm P.FullSubcategory a b).hom.app X) =
      (shiftFunctorComm C a b).hom.app X.obj := by
  letI : HasShift P.FullSubcategory A := P.hasShift
  letI : P.ι.CommShift A := P.commShiftι
  rw [P.ι.map_shiftFunctorComm_hom_app]
  rw [show P.ι.commShiftIso a =
    P.liftCompιIso (P.ι ⋙ shiftFunctor C a)
      (fun Z => P.le_shift a _ Z.property) from rfl]
  rw [show P.ι.commShiftIso b =
    P.liftCompιIso (P.ι ⋙ shiftFunctor C b)
      (fun Z => P.le_shift b _ Z.property) from rfl]
  unfold ObjectProperty.liftCompιIso
  erw [Category.id_comp, Functor.map_id, Category.id_comp,
    Functor.map_id, Category.comp_id]
  erw [Category.comp_id]
  rfl

unseal ObjectProperty.hasShift ObjectProperty.commShiftι in
private lemma iota_map_shiftComm_inv {C : Type*} [Category* C] {A : Type*}
    [AddCommMonoid A] [HasShift C A]
    (P : ObjectProperty C) [P.IsStableUnderShift A]
    (X : P.FullSubcategory) (a b : A) :
    P.ι.map ((shiftFunctorComm P.FullSubcategory a b).inv.app X) =
      (shiftFunctorComm C a b).inv.app X.obj := by
  let e := P.ι.mapIso ((shiftFunctorComm P.FullSubcategory a b).app X)
  change e.inv = (shiftFunctorComm C a b).inv.app X.obj
  have he : e.hom = (shiftFunctorComm C a b).hom.app X.obj := by
    exact iota_map_shiftComm_hom P X a b
  apply (cancel_mono e.hom).mp
  rw [e.inv_hom_id]
  rw [he]
  symm
  exact ((shiftFunctorComm C a b).app X.obj).inv_hom_id

private lemma iota_map_int_epsilon {C : Type*} [Category* C] [Preadditive C]
    [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    (P : ObjectProperty C) [P.IsStableUnderShift ℤ]
    (X : P.FullSubcategory) (m n : ℤ) :
    P.ι.map ((CommShift₂Setup.int.ε m n).val.app X) =
      (CommShift₂Setup.int.ε m n).val.app X.obj := by
  dsimp only [CommShift₂Setup.int]
  rw [CatCenter.app_neg_one_zpow, CatCenter.app_neg_one_zpow]
  simp only [Functor.map_units_smul, P.ι.map_id]
  rfl

noncomputable section

unseal ObjectProperty.hasShift ObjectProperty.commShiftι in
set_option backward.isDefEq.respectTransparency false in
/-- A coherent shift package for the restriction of a bifunctor to a
shift-stable full subcategory. This is explicit data, rather than a global
instance, so independent restricted bifunctors do not create an instance
diamond. -/
@[reducible]
def lift₂CommShift₂Int (P : ObjectProperty C) [Preadditive C]
    [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [P.IsStableUnderShift ℤ] (F : C ⥤ C ⥤ C) [F.CommShift₂Int]
    (hF : ∀ X Y, P X → P Y → P ((F.obj X).obj Y)) :
    (P.lift₂ F hF).CommShift₂Int := by
  letI : HasShift P.FullSubcategory ℤ := ObjectProperty.hasShift P
  letI (n : ℤ) : (shiftFunctor P.FullSubcategory n).Additive := by infer_instance
  letI : P.ι.CommShift ℤ := P.commShiftι
  let F' : P.FullSubcategory ⥤ P.FullSubcategory ⥤ C :=
    (P.ι ⋙ F) ⋙ (Functor.whiskeringLeft P.FullSubcategory C C).obj P.ι
  letI : F'.CommShift₂Int := by
    dsimp [F']
    infer_instance
  let hF' : ∀ X Y, P ((F'.obj X).obj Y) :=
    fun X Y => hF X.obj Y.obj X.property Y.property
  let hFlip : ∀ Y, ∀ X, P ((F'.flip.obj Y).obj X) :=
    fun Y X => by
      change P ((F'.obj X).obj Y)
      exact hF' X Y
  have hK : liftOutput P F' hF' = P.lift₂ F hF := by
    dsimp [liftOutput, F', hF']
    rfl
  rw [← hK]
  letI (X : P.FullSubcategory) : ((liftOutput P F' hF').obj X).CommShift ℤ := by
    exact Functor.CommShift.ofComp (P.liftCompιIso (F'.obj X) (hF' X)) ℤ
  letI (Y : P.FullSubcategory) : ((liftOutput P F' hF').flip.obj Y).CommShift ℤ := by
    exact Functor.CommShift.ofComp
      (P.liftCompιIso (F'.flip.obj Y) (hFlip Y)) ℤ
  refine
    { commShiftObj := fun X =>
        Functor.CommShift.ofComp (P.liftCompιIso (F'.obj X) (hF' X)) ℤ
      commShift_map := fun {X Y} f => by
        let hX : ∀ Z, P ((P.ι ⋙ F.obj X.obj).obj Z) :=
          fun Z => hF X.obj Z.obj X.property Z.property
        let hY : ∀ Z, P ((P.ι ⋙ F.obj Y.obj).obj Z) :=
          fun Z => hF Y.obj Z.obj Y.property Z.property
        let τ : P.ι ⋙ F.obj X.obj ⟶ P.ι ⋙ F.obj Y.obj :=
          Functor.whiskerLeft P.ι (F.map f.hom)
        change NatTrans.CommShift (liftNatTrans P hX hY τ) ℤ
        apply liftNatTrans_commShift
      commShiftFlipObj := fun Y =>
        Functor.CommShift.ofComp (P.liftCompιIso (F'.flip.obj Y) (hFlip Y)) ℤ
      commShift_flip_map := fun {Y Z} g => by
        let hY : ∀ X, P ((P.ι ⋙ F.flip.obj Y.obj).obj X) :=
          fun X => hF X.obj Y.obj X.property Y.property
        let hZ : ∀ X, P ((P.ι ⋙ F.flip.obj Z.obj).obj X) :=
          fun X => hF X.obj Z.obj X.property Z.property
        let τ : P.ι ⋙ F.flip.obj Y.obj ⟶ P.ι ⋙ F.flip.obj Z.obj :=
          Functor.whiskerLeft P.ι (F.flip.map g.hom)
        change NatTrans.CommShift (liftNatTrans P hY hZ τ) ℤ
        apply liftNatTrans_commShift
      comm := fun X Y m n => by
        have h := F'.commShift₂_comm .int X Y m n
        apply P.hom_ext
        change P.ι.map
          ((((P.lift (F'.obj ((shiftFunctor P.FullSubcategory m).obj X))
            (hF' ((shiftFunctor P.FullSubcategory m).obj X))).commShiftIso n).hom.app Y) ≫
            (shiftFunctor P.FullSubcategory n).map
              (((P.lift (F'.flip.obj Y) (hFlip Y)).commShiftIso m).hom.app X)) =
          P.ι.map
            ((((P.lift (F'.flip.obj ((shiftFunctor P.FullSubcategory n).obj Y))
              (hFlip ((shiftFunctor P.FullSubcategory n).obj Y))).commShiftIso m).hom.app X) ≫
              (shiftFunctor P.FullSubcategory m).map
                (((P.lift (F'.obj X) (hF' X)).commShiftIso n).hom.app Y) ≫
                (shiftFunctorComm P.FullSubcategory m n).inv.app
                  ((P.lift (F'.obj X) (hF' X)).obj Y) ≫
                  (CommShift₂Setup.int.ε m n).val.app
                    ((shiftFunctor P.FullSubcategory n).obj
                      ((shiftFunctor P.FullSubcategory m).obj
                        ((P.lift (F'.obj X) (hF' X)).obj Y))))
        simp only [Functor.map_comp]
        erw [iota_map_lift_commShift_hom P
          (F'.obj ((shiftFunctor P.FullSubcategory m).obj X))
          (hF' ((shiftFunctor P.FullSubcategory m).obj X)) Y n]
        erw [iota_map_shiftFunctor_map P _ n]
        erw [iota_map_lift_commShift_hom P (F'.flip.obj Y) (hFlip Y) X m]
        erw [iota_map_lift_commShift_hom P
          (F'.flip.obj ((shiftFunctor P.FullSubcategory n).obj Y))
          (hFlip ((shiftFunctor P.FullSubcategory n).obj Y)) X m]
        erw [iota_map_shiftFunctor_map P _ m]
        erw [iota_map_lift_commShift_hom P (F'.obj X) (hF' X) Y n]
        erw [iota_map_shiftComm_inv P ((P.lift (F'.obj X) (hF' X)).obj Y) m n]
        erw [iota_map_int_epsilon P
          ((shiftFunctor P.FullSubcategory n).obj
            ((shiftFunctor P.FullSubcategory m).obj
              ((P.lift (F'.obj X) (hF' X)).obj Y))) m n]
        exact h }

end

/-- To prove that a bifunctor preserves an isomorphism-stable object property, it suffices to
check the claim after presenting both inputs through an essentially surjective functor. -/
theorem maps₂_of_comp_of_essSurj {D : Type u'} [Category.{v'} D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (L : C ⥤ D) [L.EssSurj] (F : D ⥤ D ⥤ D) (G : C ⥤ C ⥤ D)
    (e : (((Functor.whiskeringLeft₂ D).obj L).obj L).obj F ≅ G)
    (hG : ∀ X Y, P (L.obj X) → P (L.obj Y) → P ((G.obj X).obj Y)) :
    ∀ X Y, P X → P Y → P ((F.obj X).obj Y) := by
  intro X Y hX hY
  let X' := L.objPreimage X
  let Y' := L.objPreimage Y
  let eX : L.obj X' ≅ X := L.objObjPreimageIso X
  let eY : L.obj Y' ≅ Y := L.objObjPreimageIso Y
  exact P.prop_of_iso
    (((e.app X').app Y').symm ≪≫ (F.mapIso eX).app (L.obj Y') ≪≫
      (F.obj X).mapIso eY)
    (hG X' Y' (P.prop_of_iso eX.symm hX) (P.prop_of_iso eY.symm hY))

end CategoryTheory.ObjectProperty
