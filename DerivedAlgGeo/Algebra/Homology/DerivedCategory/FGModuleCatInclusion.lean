/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.FGModuleCat.Projective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.AcyclicGenerators
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor.Bounded
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Bounded derived inclusion of finitely generated modules

Over a noetherian commutative ring, the canonical inclusion of finitely
generated modules into all modules is exact. Finite free modules cover every
finitely generated module and are projective on both sides of this inclusion.
The acyclic-generators criterion therefore compares all `Ext` groups, and
bounded dévissage makes the induced functor bijective on morphisms between
bounded derived objects.

This is a full-faithfulness statement for the bounded source inside the
unbounded derived category of all modules. It does not identify derived Hom
after localization, make the unbounded inclusion fully faithful, or assert
anything about coherent sheaves or relative geometry.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Abelian

attribute [local instance] HasDerivedCategory.standard CategoryTheory.hasExt_of_hasDerivedCategory
attribute [local instance] Abelian.hasFiniteBiproducts

noncomputable section

universe u

namespace FGModuleCat

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The exact derived functor of the canonical inclusion of finite modules
into all modules. The exactness instances are supplied locally, so importing
this leaf does not install alternative global category-theoretic instances. -/
def derivedInclusion : DerivedCategory (FGModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R) := by
  let F := (ModuleCat.isFG R).ι
  haveI : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : F.Additive := Functor.additive_of_preserves_binary_products F
  exact F.mapDerivedCategory

/-- On bounded derived objects of finitely generated modules, the inclusion
into the derived category of all modules is bijective on each morphism set. -/
theorem boundedDerivedInclusion_map_bijective
    (E E' : DerivedCategory.Bounded (FGModuleCat.{u} R)) :
    Function.Bijective
      ((DerivedCategory.Bounded.ι ⋙ (derivedInclusion (R := R))).map : (E ⟶ E') → _) := by
  let F := (ModuleCat.isFG R).ι
  haveI : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : F.Additive := Functor.additive_of_preserves_binary_products F
  have hExt (X Y : FGModuleCat.{u} R) (n : ℕ) :
      Function.Bijective (F.mapExtAddHom X Y n) := by
    apply F.bijective_mapExtAddHom_of_generators
      (fun P ↦ ∃ k, P = FGModuleCat.of R (Fin k → R))
    · intro M
      obtain ⟨k, q, hq⟩ := FGModuleCat.exists_finFree_epi M
      exact ⟨_, q, ⟨k, rfl⟩, hq⟩
    · intro P hP Y n
      obtain ⟨k, rfl⟩ := hP
      haveI := FGModuleCat.projective_of_finFree (R := R) k
      exact subsingleton_of_forall_eq 0 fun e ↦ Ext.eq_zero_of_projective e
    · intro P hP Y n
      obtain ⟨k, rfl⟩ := hP
      haveI : Projective (F.obj (FGModuleCat.of R (Fin k → R))) := by
        change Projective (ModuleCat.of R (Fin k → R))
        exact ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
      exact subsingleton_of_forall_eq 0 fun e ↦ Ext.eq_zero_of_projective e
    · intro X Y
      exact F.bijective_mapExtAddHom_zero X Y
  have hι : Function.Bijective
      ((DerivedCategory.Bounded.ι (C := FGModuleCat.{u} R)).map : (E ⟶ E') → _) :=
    ⟨DerivedCategory.Bounded.ι.map_injective,
      DerivedCategory.Bounded.ι.map_surjective⟩
  exact (F.mapDerivedCategory_map_bijective_of_bounded hExt E.property E'.property).comp hι

end FGModuleCat
