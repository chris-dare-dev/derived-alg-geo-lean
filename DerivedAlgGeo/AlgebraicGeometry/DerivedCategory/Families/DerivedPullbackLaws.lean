/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPullbackCoherence

/-!
# Pseudofunctor laws for exact derived pullback

The complex-level pullback unit and associativity laws are inherited degreewise
from Mathlib's module-sheaf pullback pseudofunctor.  Localization then transports
those laws to exact pullback on the concrete derived fibers.  Equality congruence
is lifted through the same localization so the laws have canonical, typed
right-hand sides even when composition is only propositionally equal.

This file proves the left-unit, right-unit, and associativity (pentagon) laws for
the exact derived pullback compositor.  It does not yet prove compatibility of
these isomorphisms with the triangulated shift, characterize exact pullback by a
geometric flatness criterion, or construct nonexact left-derived pullback.
-/

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem complexPullback_associativity
    {T U V W : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) (h : V ⟶ W) :
    (complexPullbackComp f (g ≫ h)).inv ≫
      CategoryTheory.Functor.whiskerRight (complexPullbackComp g h).inv _ ≫
        (CategoryTheory.Functor.associator _ _ _).hom ≫
          CategoryTheory.Functor.whiskerLeft _ (complexPullbackComp f g).hom ≫
            (complexPullbackComp (f ≫ g) h).hom =
      eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  exact congr_app
    (Scheme.Modules.pseudofunctor_associativity f.left g.left h.left)
    (K.X n)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem complexPullback_left_unitality
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    (complexPullbackComp f (𝟙 U)).inv ≫
      CategoryTheory.Functor.whiskerRight (complexPullbackId U).hom (complexPullback f) ≫
        (CategoryTheory.Functor.leftUnitor _).hom =
      eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  exact congr_app
    (Scheme.Modules.pseudofunctor_left_unitality f.left)
    (K.X n)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem complexPullback_right_unitality
    {T U : SchemeBaseChange S} (f : T ⟶ U) :
    (complexPullbackComp (𝟙 T) f).inv ≫
      CategoryTheory.Functor.whiskerLeft (complexPullback f) (complexPullbackId T).hom ≫
        (CategoryTheory.Functor.rightUnitor _).hom =
      eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.Hom.ext
  funext n
  exact congr_app
    (Scheme.Modules.pseudofunctor_right_unitality f.left)
    (K.X n)

/-- Equality of scheme base-change morphisms induces a canonical isomorphism
between their pullback functors on cochain complexes. -/
def complexPullbackCongr {T U : SchemeBaseChange S}
    {f g : T ⟶ U} (h : f = g) :
    complexPullback f ≅ complexPullback g := by
  subst g
  exact Iso.refl _

/-- Equality of exact scheme base-change morphisms induces a canonical
isomorphism between their derived pullback functors. -/
def derivedPullbackCongr {T U : SchemeBaseChange S}
    {f g : T ⟶ U} [IsExactPullback f] [IsExactPullback g]
    (h : f = g) : derivedPullback f ≅ derivedPullback g := by
  letI : Localization.Lifting (SchemeDerivedCategory.Q U.left)
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
      (complexPullback f ⋙ SchemeDerivedCategory.Q T.left)
      (derivedPullback f) := ⟨derivedPullbackFactors f⟩
  letI : Localization.Lifting (SchemeDerivedCategory.Q U.left)
      (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
      (complexPullback g ⋙ SchemeDerivedCategory.Q T.left)
      (derivedPullback g) := ⟨derivedPullbackFactors g⟩
  exact Localization.liftNatIso (SchemeDerivedCategory.Q U.left)
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
    (complexPullback f ⋙ SchemeDerivedCategory.Q T.left)
    (complexPullback g ⋙ SchemeDerivedCategory.Q T.left)
    (derivedPullback f) (derivedPullback g)
    (CategoryTheory.Functor.isoWhiskerRight (complexPullbackCongr h)
      (SchemeDerivedCategory.Q T.left))

set_option backward.isDefEq.respectTransparency false in
set_option linter.tacticCheckInstances false in
@[reassoc]
theorem derivedPullback_left_unitality
    {T U : SchemeBaseChange S} (f : T ⟶ U) [IsExactPullback f] :
    (derivedPullbackComp f (𝟙 U)).inv ≫
      CategoryTheory.Functor.whiskerRight (derivedPullbackId U).hom (derivedPullback f) ≫
        (CategoryTheory.Functor.leftUnitor _).hom =
      (derivedPullbackCongr (Category.comp_id f)).hom := by
  apply Localization.natTrans_ext (SchemeDerivedCategory.Q U.left)
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
  intro K
  have hcomplexBase :
      (complexPullbackComp f (𝟙 U)).inv.app K ≫
          (complexPullback f).map ((complexPullbackId U).hom.app K) =
        eqToHom (by simp) := by
    calc
      _ = (complexPullbackComp f (𝟙 U)).inv.app K ≫
          (complexPullback f).map ((complexPullbackId U).hom.app K) ≫
            𝟙 _ := (Category.comp_id _).symm
      _ = _ := congr_app (complexPullback_left_unitality f) K
  have hcomplex := congrArg (SchemeDerivedCategory.Q T.left).map hcomplexBase
  simp only [CategoryTheory.Functor.map_comp] at hcomplex
  have hnat := (derivedPullbackFactors f).inv.naturality
    ((complexPullbackId U).hom.app K)
  simp [derivedPullbackComp, derivedPullbackId,
    Localization.liftNatTrans_app, complexPullbackIdLocalized,
    complexPullbackCompLocalized, derivedPullbackCongr]
  slice_lhs 3 6 =>
    rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  slice_lhs 4 5 => simp
  slice_lhs 2 3 => erw [← hnat]
  slice_lhs 1 2 => erw [hcomplex]
  slice_lhs 2 4 => simp
  simp [complexPullbackCongr]
  slice_lhs 3 4 => erw [CategoryTheory.Functor.map_id, Category.comp_id]
  slice_lhs 2 3 => erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option linter.tacticCheckInstances false in
@[reassoc]
theorem derivedPullback_right_unitality
    {T U : SchemeBaseChange S} (f : T ⟶ U) [IsExactPullback f] :
    (derivedPullbackComp (𝟙 T) f).inv ≫
      CategoryTheory.Functor.whiskerLeft (derivedPullback f) (derivedPullbackId T).hom ≫
        (CategoryTheory.Functor.rightUnitor _).hom =
      (derivedPullbackCongr (Category.id_comp f)).hom := by
  apply Localization.natTrans_ext (SchemeDerivedCategory.Q U.left)
    (HomologicalComplex.quasiIso U.left.Modules (ComplexShape.up ℤ))
  intro K
  have hcomplexBase :
      (complexPullbackComp (𝟙 T) f).inv.app K ≫
          (complexPullbackId T).hom.app ((complexPullback f).obj K) =
        eqToHom (by simp) := by
    calc
      _ = (complexPullbackComp (𝟙 T) f).inv.app K ≫
          (complexPullbackId T).hom.app ((complexPullback f).obj K) ≫
            𝟙 _ := (Category.comp_id _).symm
      _ = _ := congr_app (complexPullback_right_unitality f) K
  have hcomplex := congrArg (SchemeDerivedCategory.Q T.left).map hcomplexBase
  simp only [CategoryTheory.Functor.map_comp] at hcomplex
  have hnat := (derivedPullbackId T).hom.naturality
    ((derivedPullbackFactors f).inv.app K)
  have heta :
      (derivedPullbackId T).hom.app
          ((SchemeDerivedCategory.Q T.left).obj ((complexPullback f).obj K)) =
        (derivedPullbackFactors (𝟙 T)).hom.app ((complexPullback f).obj K) ≫
          (complexPullbackIdLocalized T).hom.app ((complexPullback f).obj K) ≫
            (CategoryTheory.Functor.rightUnitor (SchemeDerivedCategory.Q T.left)).inv.app
              ((complexPullback f).obj K) := by
    simp [derivedPullbackId, Localization.liftNatTrans_app]
  simp [derivedPullbackComp, derivedPullbackId,
    Localization.liftNatTrans_app, complexPullbackIdLocalized,
    complexPullbackCompLocalized, derivedPullbackCongr]
  slice_lhs 4 5 => erw [Category.comp_id]
  slice_lhs 3 4 => erw [hnat]
  slice_lhs 2 3 => erw [heta]
  slice_lhs 2 3 => rw [Iso.inv_hom_id_app]
  slice_lhs 2 4 => simp [complexPullbackIdLocalized]
  slice_lhs 1 2 => erw [Category.comp_id]
  slice_lhs 1 2 => erw [hcomplex]
  slice_lhs 2 3 => erw [Category.id_comp]
  simp [complexPullbackCongr]

set_option backward.isDefEq.respectTransparency false in
set_option linter.tacticCheckInstances false in
@[reassoc]
theorem derivedPullback_associativity
    {T U V W : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) (h : V ⟶ W)
    [IsExactPullback f] [IsExactPullback g] [IsExactPullback h] :
    (derivedPullbackComp f (g ≫ h)).inv ≫
      CategoryTheory.Functor.whiskerRight (derivedPullbackComp g h).inv
        (derivedPullback f) ≫
        (CategoryTheory.Functor.associator _ _ _).hom ≫
          CategoryTheory.Functor.whiskerLeft (derivedPullback h)
            (derivedPullbackComp f g).hom ≫
            (derivedPullbackComp (f ≫ g) h).hom =
      (derivedPullbackCongr (by simp)).hom := by
  apply Localization.natTrans_ext (SchemeDerivedCategory.Q W.left)
    (HomologicalComplex.quasiIso W.left.Modules (ComplexShape.up ℤ))
  intro K
  have hcomplexBase :
      (complexPullbackComp f (g ≫ h)).inv.app K ≫
        (complexPullback f).map ((complexPullbackComp g h).inv.app K) ≫
          (complexPullbackComp f g).hom.app ((complexPullback h).obj K) ≫
            (complexPullbackComp (f ≫ g) h).hom.app K =
        (complexPullbackCongr (by simp)).hom.app K := by
    simpa [complexPullbackCongr] using
      congr_app (complexPullback_associativity f g h) K
  have hcomplex := congrArg (SchemeDerivedCategory.Q T.left).map hcomplexBase
  simp only [CategoryTheory.Functor.map_comp] at hcomplex
  have hcomplexTail :
      (SchemeDerivedCategory.Q T.left).map
          ((complexPullbackComp f (g ≫ h)).inv.app K) ≫
        (SchemeDerivedCategory.Q T.left).map
            ((complexPullback f).map ((complexPullbackComp g h).inv.app K)) ≫
          (SchemeDerivedCategory.Q T.left).map
              ((complexPullbackComp f g).hom.app ((complexPullback h).obj K)) ≫
            (SchemeDerivedCategory.Q T.left).map
                ((complexPullbackComp (f ≫ g) h).hom.app K) ≫
              (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K =
        (SchemeDerivedCategory.Q T.left).map
            ((complexPullbackCongr (by simp)).hom.app K) ≫
          (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K := by
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K)
      hcomplex
  have halpha :
      (derivedPullbackComp f g).hom.app
          ((SchemeDerivedCategory.Q V.left).obj ((complexPullback h).obj K)) =
        (derivedPullback f).map
            ((derivedPullbackFactors g).hom.app ((complexPullback h).obj K)) ≫
          (complexPullbackCompLocalized f g).hom.app ((complexPullback h).obj K) ≫
            (derivedPullbackFactors (f ≫ g)).inv.app ((complexPullback h).obj K) := by
    simp [derivedPullbackComp, Localization.liftNatTrans_app]
  have hnat := (derivedPullbackComp f g).hom.naturality
    ((derivedPullbackFactors h).inv.app K)
  have hmove :
      (derivedPullback f).map
          ((SchemeDerivedCategory.Q U.left).map
            ((complexPullbackComp g h).inv.app K)) ≫
        (derivedPullbackFactors f).hom.app
            ((complexPullback h ⋙ complexPullback g).obj K) ≫
          (SchemeDerivedCategory.Q T.left).map
              ((complexPullbackComp f g).hom.app ((complexPullback h).obj K)) ≫
            (SchemeDerivedCategory.Q T.left).map
                ((complexPullbackComp (f ≫ g) h).hom.app K) ≫
              (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K =
        (derivedPullbackFactors f).hom.app ((complexPullback (g ≫ h)).obj K) ≫
          (SchemeDerivedCategory.Q T.left).map
              ((complexPullback f).map ((complexPullbackComp g h).inv.app K)) ≫
            (SchemeDerivedCategory.Q T.left).map
                ((complexPullbackComp f g).hom.app ((complexPullback h).obj K)) ≫
              (SchemeDerivedCategory.Q T.left).map
                  ((complexPullbackComp (f ≫ g) h).hom.app K) ≫
                (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K := by
    simpa using (derivedPullbackFactors f).hom.naturality_assoc
      ((complexPullbackComp g h).inv.app K)
      ((SchemeDerivedCategory.Q T.left).map
          ((complexPullbackComp f g).hom.app ((complexPullback h).obj K)) ≫
        (SchemeDerivedCategory.Q T.left).map
            ((complexPullbackComp (f ≫ g) h).hom.app K) ≫
          (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K)
  simp [derivedPullbackComp, Localization.liftNatTrans_app,
    complexPullbackCompLocalized, derivedPullbackCongr]
  rw [← (derivedPullback f).map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  slice_lhs 5 8 => erw [hnat]
  have hcancel :
      ((derivedPullbackComp f g).hom.app
          ((complexPullback h ⋙ SchemeDerivedCategory.Q V.left).obj K) ≫
        (derivedPullback (f ≫ g)).map ((derivedPullbackFactors h).inv.app K)) ≫
          (derivedPullback (f ≫ g)).map ((derivedPullbackFactors h).hom.app K) =
        (derivedPullbackComp f g).hom.app
          ((complexPullback h ⋙ SchemeDerivedCategory.Q V.left).obj K) := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hcancelg :
      (derivedPullback f).map
          ((derivedPullbackFactors g).inv.app ((complexPullback h).obj K)) ≫
        (derivedPullback f).map
            ((derivedPullbackFactors g).hom.app ((complexPullback h).obj K)) ≫
          (derivedPullbackFactors f).hom.app
              ((complexPullback g).obj ((complexPullback h).obj K)) ≫
            (SchemeDerivedCategory.Q T.left).map
                ((complexPullbackComp f g).hom.app ((complexPullback h).obj K)) ≫
            (SchemeDerivedCategory.Q T.left).map
                ((complexPullbackComp (f ≫ g) h).hom.app K) ≫
              (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K =
        (derivedPullbackFactors f).hom.app
            ((complexPullback g).obj ((complexPullback h).obj K)) ≫
          (SchemeDerivedCategory.Q T.left).map
              ((complexPullbackComp f g).hom.app ((complexPullback h).obj K)) ≫
          (SchemeDerivedCategory.Q T.left).map
              ((complexPullbackComp (f ≫ g) h).hom.app K) ≫
            (derivedPullbackFactors ((f ≫ g) ≫ h)).inv.app K := by
    rw [← (derivedPullback f).map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hcancel]
  erw [halpha]
  simp [complexPullbackCompLocalized]
  erw [hcancelg]
  erw [hmove]
  rw [Iso.inv_hom_id_app_assoc]
  exact hcomplexTail

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
