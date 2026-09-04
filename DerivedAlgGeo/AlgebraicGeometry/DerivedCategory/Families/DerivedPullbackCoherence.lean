/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ExactPullbackCoherence

/-!
# Derived coherence for exact scheme pullback

The identity and composition isomorphisms for exact pullback descend through
the derived-category localization.  This supplies the unit and composition
isomorphisms for the contravariant assignment sending a scheme base change to
its derived category of module sheaves.

This file does not yet prove the triangle and pentagon coherence equations for
those isomorphisms, characterize exactness geometrically, construct a
left-derived functor for nonexact pullback, or restrict the construction to
bounded coherent or perfect complexes.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The complex-level identity isomorphism, followed by localization. -/
def complexPullbackIdLocalized (T : SchemeBaseChange S) :
    complexPullback (𝟙 T) ⋙ SchemeDerivedCategory.Q T.left ≅
      SchemeDerivedCategory.Q T.left :=
  CategoryTheory.Functor.isoWhiskerRight (complexPullbackId T)
      (SchemeDerivedCategory.Q T.left) ≪≫
    CategoryTheory.Functor.leftUnitor (SchemeDerivedCategory.Q T.left)

/-- Exact derived pullback along an identity is naturally isomorphic to the
identity functor. -/
def derivedPullbackId (T : SchemeBaseChange S) :
    derivedPullback (𝟙 T) ≅ 𝟭 T.DerivedFiber := by
  letI : Localization.Lifting (SchemeDerivedCategory.Q T.left)
      (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
      (complexPullback (𝟙 T) ⋙ SchemeDerivedCategory.Q T.left)
      (derivedPullback (𝟙 T)) :=
    ⟨derivedPullbackFactors (𝟙 T)⟩
  exact Localization.liftNatIso (SchemeDerivedCategory.Q T.left)
    (HomologicalComplex.quasiIso T.left.Modules (ComplexShape.up ℤ))
    (complexPullback (𝟙 T) ⋙ SchemeDerivedCategory.Q T.left)
    (SchemeDerivedCategory.Q T.left)
    (derivedPullback (𝟙 T)) (𝟭 T.DerivedFiber)
    (complexPullbackIdLocalized T)

/-- The complex-level composition isomorphism, followed by localization. -/
def complexPullbackCompLocalized {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) [IsExactPullback f] :
    (complexPullback g ⋙ SchemeDerivedCategory.Q U.left) ⋙
        derivedPullback f ≅
      complexPullback (f ≫ g) ⋙ SchemeDerivedCategory.Q T.left :=
  CategoryTheory.Functor.associator _ _ _ ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (complexPullback g) (derivedPullbackFactors f) ≪≫
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
    CategoryTheory.Functor.isoWhiskerRight (complexPullbackComp f g)
      (SchemeDerivedCategory.Q T.left)

/-- The composite of two exact derived pullbacks is naturally isomorphic to
derived pullback along the composite scheme morphism. -/
def derivedPullbackComp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) [IsExactPullback f] [IsExactPullback g] :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) := by
  letI : Localization.Lifting (SchemeDerivedCategory.Q V.left)
      (HomologicalComplex.quasiIso V.left.Modules (ComplexShape.up ℤ))
      (complexPullback g ⋙ SchemeDerivedCategory.Q U.left)
      (derivedPullback g) :=
    ⟨derivedPullbackFactors g⟩
  letI : Localization.Lifting (SchemeDerivedCategory.Q V.left)
      (HomologicalComplex.quasiIso V.left.Modules (ComplexShape.up ℤ))
      ((complexPullback g ⋙ SchemeDerivedCategory.Q U.left) ⋙
        derivedPullback f)
      (derivedPullback g ⋙ derivedPullback f) := inferInstance
  letI : Localization.Lifting (SchemeDerivedCategory.Q V.left)
      (HomologicalComplex.quasiIso V.left.Modules (ComplexShape.up ℤ))
      (complexPullback (f ≫ g) ⋙ SchemeDerivedCategory.Q T.left)
      (derivedPullback (f ≫ g)) :=
    ⟨derivedPullbackFactors (f ≫ g)⟩
  exact Localization.liftNatIso (SchemeDerivedCategory.Q V.left)
    (HomologicalComplex.quasiIso V.left.Modules (ComplexShape.up ℤ))
    ((complexPullback g ⋙ SchemeDerivedCategory.Q U.left) ⋙
      derivedPullback f)
    (complexPullback (f ≫ g) ⋙ SchemeDerivedCategory.Q T.left)
    (derivedPullback g ⋙ derivedPullback f) (derivedPullback (f ≫ g))
    (complexPullbackCompLocalized f g)

@[simp]
theorem derivedPullK₀_id (T : SchemeBaseChange S) :
    derivedPullK₀ (𝟙 T) = AddMonoidHom.id (K₀ T.DerivedFiber) := by
  change K₀.map (derivedPullback (𝟙 T)) =
    AddMonoidHom.id (K₀ T.DerivedFiber)
  rw [K₀.map_congr (derivedPullbackId T), K₀.map_id]

@[simp]
theorem derivedPullK₀_comp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V) [IsExactPullback f] [IsExactPullback g] :
    derivedPullK₀ (f ≫ g) =
      (derivedPullK₀ f).comp (derivedPullK₀ g) := by
  change K₀.map (derivedPullback (f ≫ g)) =
    (K₀.map (derivedPullback f)).comp (K₀.map (derivedPullback g))
  rw [← K₀.map_congr (derivedPullbackComp f g), K₀.map_comp]

end SchemeBaseChange

end

end AlgebraicGeometry.DerivedCategory.Families
