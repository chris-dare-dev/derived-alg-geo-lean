/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Descent.LevelPushforward
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback

/-!
# Cartesian objects of the derived category of the total site

Restriction to a level `g_n⁻¹` is exact (it has both adjoints), so it induces
`K ↦ K_n` on derived categories. For `φ : [n] ⟶ [m]` there is a natural
comparison `L X(φ)^* K_n ⟶ K_m`, where `L X(φ)^*` is the repository's
left-derived pullback along the arbitrary morphism `X(φ) : X_m ⟶ X_n`. An object
is cartesian when all of these comparisons are isomorphisms (Stacks,
Definition 85.12.1, Tag 0D7G; Section 85.14).

The comparison is defined on complexes as the derived-pullback counit followed by
the degreewise comparison `X(φ)^* F_n ⟶ F_m` of `TotalSite.transitionPullback`,
and descended to the derived category through the localization.

## Main definitions

* `AlgebraicGeometry.TotalSite.derivedRestrict X n`: `K ↦ K_n`.
* `AlgebraicGeometry.TotalSite.derivedTransition X φ`: `L X(φ)^* K_n ⟶ K_m`.
* `AlgebraicGeometry.TotalSite.IsCartesianObj X`.
-/

attribute [local instance] HasDerivedCategory.standard

universe u

open CategoryTheory Opposite Limits
open AlgebraicGeometry.DerivedCategory AlgebraicGeometry.DerivedCategory.Families

namespace AlgebraicGeometry.TotalSite

variable (X : SimplicialObject Scheme.{u})

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts in
instance (n : SimplexCategory) : (restrict X n).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- `K ↦ K_n`: restriction to the level `n` on derived categories. -/
noncomputable def derivedRestrict (n : SimplexCategory) :
    _root_.DerivedCategory (Modules X) ⥤ SchemeDerivedCategory (X.obj (op n)) :=
  (restrict X n).mapDerivedCategory

/-- `X(φ) : X_m ⟶ X_n` as a morphism of schemes over `X_n`. -/
def transitionOver {n m : SimplexCategory} (φ : n ⟶ m) :
    (Over.mk (X.map φ.op) : SchemeBaseChange (X.obj (op n))) ⟶ Over.mk (𝟙 _) :=
  Over.homMk (X.map φ.op)

/-- The left-derived pullback `L X(φ)^*` along `X(φ) : X_m ⟶ X_n`. -/
noncomputable def derivedTransitionPullback {n m : SimplexCategory} (φ : n ⟶ m) :
    SchemeDerivedCategory (X.obj (op n)) ⥤ SchemeDerivedCategory (X.obj (op m)) :=
  (SchemeBaseChange.arbitraryLeftDerivedPullback (transitionOver X φ)).functor

/-- The comparison `L X(φ)^* K_n ⟶ K_m` after composing with the localization
functor from cochain complexes. -/
noncomputable def derivedTransitionAux {n m : SimplexCategory} (φ : n ⟶ m) :
    _root_.DerivedCategory.Q ⋙ derivedRestrict X n ⋙ derivedTransitionPullback X φ ⟶
      _root_.DerivedCategory.Q ⋙ derivedRestrict X m :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (restrict X n).mapDerivedCategoryFactors.hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((restrict X n).mapHomologicalComplex _)
      (SchemeBaseChange.arbitraryLeftDerivedPullback (transitionOver X φ)).counit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (NatTrans.mapHomologicalComplex (transitionPullback X φ) _ :
      (restrict X n).mapHomologicalComplex _ ⋙
        SchemeBaseChange.complexPullback (transitionOver X φ) ⟶ _)
      _root_.DerivedCategory.Q ≫
    (restrict X m).mapDerivedCategoryFactors.inv

/-- The comparison `L X(φ)^* K_n ⟶ K_m` of Stacks, Definition 85.12.1 (Tag 0D7G). -/
noncomputable def derivedTransition {n m : SimplexCategory} (φ : n ⟶ m) :
    derivedRestrict X n ⋙ derivedTransitionPullback X φ ⟶ derivedRestrict X m :=
  Localization.liftNatTrans _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso (Modules X) (ComplexShape.up ℤ)) _ _ _ _
    (derivedTransitionAux X φ)

/-- Cartesian objects of `D(𝒪_total)` (Stacks, Definition 85.12.1, Tag 0D7G): the
comparisons `L X(φ)^* K_n ⟶ K_m` are isomorphisms for every `φ`. -/
def IsCartesianObj : ObjectProperty (_root_.DerivedCategory (Modules X)) :=
  fun K => ∀ ⦃n m : SimplexCategory⦄ (φ : n ⟶ m), IsIso ((derivedTransition X φ).app K)

end AlgebraicGeometry.TotalSite
