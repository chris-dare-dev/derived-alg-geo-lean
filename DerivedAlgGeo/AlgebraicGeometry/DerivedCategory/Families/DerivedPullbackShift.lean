/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPullbackLaws

/-!
# Shift compatibility for exact derived pullback coherence

The localization factors, complex-level unit and compositor, and their localized
forms commute with the integer shift.  Consequently the unit and compositor of
exact derived pullback commute with shift as well.

The compositor proof treats the two parenthesizations of a composite explicitly:
the corresponding `CategoryTheory.Functor.CommShift` structures are not definitionally the same,
even though the underlying composite functors are.  Naturality of the final
pullback's shift isomorphism bridges that distinction before localization
extensionality completes the proof.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The localization comparison for exact derived pullback commutes with shift. -/
instance derivedPullbackFactors_commShift {T U : SchemeBaseChange S}
    (f : T ⟶ U) [IsExactPullback f] :
    NatTrans.CommShift (derivedPullbackFactors f).hom ℤ := by
  change NatTrans.CommShift ((modulePullback f).mapDerivedCategoryFactors).hom ℤ
  infer_instance

/-- The complex-level identity pullback isomorphism commutes with shift. -/
instance complexPullbackId_commShift (T : SchemeBaseChange S) :
    NatTrans.CommShift (complexPullbackId T).hom ℤ := by
  constructor
  intro a
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext i
  dsimp [complexPullbackId]
  erw [Category.id_comp]

/-- The complex-level pullback compositor commutes with shift. -/
instance complexPullbackComp_commShift {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) :
    NatTrans.CommShift (complexPullbackComp f g).hom ℤ := by
  constructor
  intro a
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext i
  dsimp [complexPullbackComp]
  simp [CategoryTheory.Functor.commShiftIso_comp_hom_app,
    CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The localized complex-level identity isomorphism commutes with shift. -/
instance complexPullbackIdLocalized_commShift (T : SchemeBaseChange S) :
    NatTrans.CommShift (complexPullbackIdLocalized T).hom ℤ := by
  change NatTrans.CommShift
    (CategoryTheory.Functor.whiskerRight (complexPullbackId T).hom
      (SchemeDerivedCategory.Q T.left) ≫
        (CategoryTheory.Functor.leftUnitor (SchemeDerivedCategory.Q T.left)).hom) ℤ
  infer_instance

/-- The localized complex-level pullback compositor commutes with shift. -/
instance complexPullbackCompLocalized_commShift
    {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsExactPullback f] :
    NatTrans.CommShift (complexPullbackCompLocalized f g).hom ℤ := by
  change NatTrans.CommShift
    ((CategoryTheory.Functor.associator _ _ _).hom ≫
      CategoryTheory.Functor.whiskerLeft (complexPullback g) (derivedPullbackFactors f).hom ≫
        (CategoryTheory.Functor.associator _ _ _).inv ≫
          CategoryTheory.Functor.whiskerRight (complexPullbackComp f g).hom
            (SchemeDerivedCategory.Q T.left)) ℤ
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option linter.tacticCheckInstances false in
/-- The unit isomorphism for exact derived pullback commutes with shift. -/
instance derivedPullbackId_commShift (T : SchemeBaseChange S) :
    NatTrans.CommShift (derivedPullbackId T).hom ℤ := by
  constructor
  intro a
  apply Localization.natTrans_ext (SchemeDerivedCategory.Q T.left)
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
  intro K
  dsimp
  simp only [CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app]
  let q := ((SchemeDerivedCategory.Q T.left).commShiftIso a).hom.app K
  have happ (X : CochainComplex T.left.Modules ℤ) :
      (derivedPullbackId T).hom.app
          ((SchemeDerivedCategory.Q T.left).obj X) =
        (derivedPullbackFactors (𝟙 T)).hom.app X ≫
          (complexPullbackIdLocalized T).hom.app X := by
    simp [derivedPullbackId, Localization.liftNatTrans_app]
  have hnat := (derivedPullbackId T).hom.naturality q
  have hsource :
      (derivedPullback (𝟙 T)).map q ≫
        ((derivedPullback (𝟙 T)).commShiftIso a).hom.app
            ((SchemeDerivedCategory.Q T.left).obj K) ≫
          (shiftFunctor T.DerivedFiber a).map
              ((derivedPullbackFactors (𝟙 T)).hom.app K) ≫
            (shiftFunctor T.DerivedFiber a).map
                ((complexPullbackIdLocalized T).hom.app K) =
        ((SchemeDerivedCategory.Q T.left ⋙
            derivedPullback (𝟙 T)).commShiftIso a).hom.app K ≫
          (shiftFunctor T.DerivedFiber a).map
              ((derivedPullbackFactors (𝟙 T)).hom.app K) ≫
            (shiftFunctor T.DerivedFiber a).map
                ((complexPullbackIdLocalized T).hom.app K) := by
    dsimp [q]
    rw [CategoryTheory.Functor.commShiftIso_comp_hom_app]
    exact (Category.assoc _ _ _).symm
  have hnatTail :
      (derivedPullback (𝟙 T)).map q ≫
        (derivedPullbackId T).hom.app
            ((shiftFunctor T.DerivedFiber a).obj
              ((SchemeDerivedCategory.Q T.left).obj K)) ≫
          ((𝟭 T.DerivedFiber).commShiftIso a).hom.app
            ((SchemeDerivedCategory.Q T.left).obj K) =
        (derivedPullbackId T).hom.app
            ((SchemeDerivedCategory.Q T.left).obj
              ((shiftFunctor (CochainComplex T.left.Modules ℤ) a).obj K)) ≫
          q := by
    rw [← Category.assoc]
    erw [hnat]
    simp
    rfl
  dsimp [q] at hnat ⊢
  rw [← cancel_epi ((derivedPullback (𝟙 T)).map
    q)]
  rw [happ, CategoryTheory.Functor.map_comp]
  rw [hsource]
  rw [NatTrans.shift_app_comm_assoc
    (derivedPullbackFactors (𝟙 T)).hom a K]
  rw [NatTrans.shift_app_comm (complexPullbackIdLocalized T).hom a K]
  rw [hnatTail]
  erw [happ]
  rw [← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option linter.tacticCheckInstances false in
/-- The compositor isomorphism for exact derived pullback commutes with shift. -/
instance derivedPullbackComp_commShift
    {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsExactPullback f] [IsExactPullback g] :
    NatTrans.CommShift (derivedPullbackComp f g).hom ℤ := by
  constructor
  intro a
  apply Localization.natTrans_ext (SchemeDerivedCategory.Q V.left)
    (HomologicalComplex.quasiIso V.left.Modules (ComplexShape.up ℤ))
  intro K
  dsimp
  simp only [CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app]
  let q := ((SchemeDerivedCategory.Q V.left).commShiftIso a).hom.app K
  let sourceFactor :
      SchemeDerivedCategory.Q V.left ⋙
          (derivedPullback g ⋙ derivedPullback f) ⟶
        (complexPullback g ⋙ SchemeDerivedCategory.Q U.left) ⋙
          derivedPullback f :=
    (CategoryTheory.Functor.associator _ _ _).hom ≫
      CategoryTheory.Functor.whiskerRight (derivedPullbackFactors g).hom
        (derivedPullback f)
  letI hFactors : NatTrans.CommShift (derivedPullbackFactors g).hom ℤ :=
    derivedPullbackFactors_commShift g
  have happ (X : CochainComplex V.left.Modules ℤ) :
      (derivedPullbackComp f g).hom.app
          ((SchemeDerivedCategory.Q V.left).obj X) =
        sourceFactor.app X ≫
          (complexPullbackCompLocalized f g).hom.app X ≫
            (derivedPullbackFactors (f ≫ g)).inv.app X := by
    simp [sourceFactor, derivedPullbackComp, Localization.liftNatTrans_app]
    erw [Category.id_comp]
  have hnat := (derivedPullbackComp f g).hom.naturality q
  have hsource :
      (derivedPullback g ⋙ derivedPullback f).map q ≫
        ((derivedPullback g ⋙ derivedPullback f).commShiftIso a).hom.app
            ((SchemeDerivedCategory.Q V.left).obj K) ≫
          (shiftFunctor T.DerivedFiber a).map
              (sourceFactor.app K) ≫
            (shiftFunctor T.DerivedFiber a).map
                ((complexPullbackCompLocalized f g).hom.app K) ≫
              (shiftFunctor T.DerivedFiber a).map
                  ((derivedPullbackFactors (f ≫ g)).inv.app K) =
        ((SchemeDerivedCategory.Q V.left ⋙ derivedPullback g ⋙
            derivedPullback f).commShiftIso a).hom.app K ≫
          (shiftFunctor T.DerivedFiber a).map
              (sourceFactor.app K) ≫
            (shiftFunctor T.DerivedFiber a).map
                ((complexPullbackCompLocalized f g).hom.app K) ≫
              (shiftFunctor T.DerivedFiber a).map
                  ((derivedPullbackFactors (f ≫ g)).inv.app K) := by
    dsimp [q]
    simp only [CategoryTheory.Functor.commShiftIso_comp_hom_app, CategoryTheory.Functor.comp_map,
      Category.assoc]
  have hsourceFactor :
      ((SchemeDerivedCategory.Q V.left ⋙ derivedPullback g ⋙
          derivedPullback f).commShiftIso a).hom.app K ≫
        (shiftFunctor T.DerivedFiber a).map (sourceFactor.app K) =
      sourceFactor.app
          ((shiftFunctor (CochainComplex V.left.Modules ℤ) a).obj K) ≫
        (((complexPullback g ⋙ SchemeDerivedCategory.Q U.left) ⋙
          derivedPullback f).commShiftIso a).hom.app K := by
    dsimp [sourceFactor]
    simp only [CategoryTheory.Functor.commShiftIso_comp_hom_app,
      CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.whiskerRight_app,
      CategoryTheory.Functor.comp_map]
    have hdf := ((derivedPullback f).commShiftIso a).hom.naturality
      ((derivedPullbackFactors g).hom.app K)
    have hfactor := NatTrans.shift_app_comm
      (derivedPullbackFactors g).hom a K
    simp only [CategoryTheory.Functor.commShiftIso_comp_hom_app] at hfactor
    erw [Category.id_comp]
    simp only [Category.assoc]
    erw [← hdf]
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc]
    erw [← CategoryTheory.Functor.map_comp_assoc]
    rw [hfactor]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [Category.id_comp]
  have hnatTail :
      (derivedPullback g ⋙ derivedPullback f).map q ≫
        (derivedPullbackComp f g).hom.app
            ((shiftFunctor V.DerivedFiber a).obj
              ((SchemeDerivedCategory.Q V.left).obj K)) ≫
          ((derivedPullback (f ≫ g)).commShiftIso a).hom.app
            ((SchemeDerivedCategory.Q V.left).obj K) =
        (derivedPullbackComp f g).hom.app
            ((SchemeDerivedCategory.Q V.left).obj
              ((shiftFunctor (CochainComplex V.left.Modules ℤ) a).obj K)) ≫
          (derivedPullback (f ≫ g)).map q ≫
            ((derivedPullback (f ≫ g)).commShiftIso a).hom.app
              ((SchemeDerivedCategory.Q V.left).obj K) := by
    rw [← Category.assoc]
    erw [hnat]
    rw [Category.assoc]
    rfl
  dsimp [q] at hnat ⊢
  rw [← cancel_epi ((derivedPullback g ⋙ derivedPullback f).map
    q)]
  rw [happ, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  erw [hsource]
  rw [reassoc_of% hsourceFactor]
  rw [NatTrans.shift_app_comm_assoc
    (complexPullbackCompLocalized f g).hom a K]
  rw [NatTrans.shift_app_comm (derivedPullbackFactors (f ≫ g)).inv a K]
  rw [CategoryTheory.Functor.commShiftIso_comp_hom_app]
  rw [hnatTail]
  erw [happ]
  simp only [Category.assoc]
  simp only [q]

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
